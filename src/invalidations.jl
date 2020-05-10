export @snoopr, invalidation_trees, explain

# This doesn't technically have to be mutable but it's more convenient for testing equality
mutable struct InstanceTree
    mi::MethodInstance
    depth::Int32
    children::Vector{InstanceTree}
    parent::InstanceTree

    # Create tree root
    function InstanceTree(mi::MethodInstance)
        new(mi, Int32(0), InstanceTree[])
    end
    # Create child
    function InstanceTree(mi::MethodInstance, depth, children, parent)
        new(mi, depth, children, parent)
    end
end
InstanceTree(mi::MethodInstance, parent::InstanceTree) = InstanceTree(mi, parent.depth+Int32(1), InstanceTree[], parent)

function getroot(node::InstanceTree)
    while isdefined(node, :parent)
        node = node.parent
    end
    return node
end

struct Invalidations
    mt_backedges::Vector{Pair{Any,InstanceTree}}   # sig=>tree
    tables::Vector{MethodInstance}
    backedges::Vector{Pair{MethodInstance,InstanceTree}}
end
Invalidations() = Invalidations(Pair{Any,InstanceTree}[], MethodInstance[], InstanceTree[])

struct MethodInvalidations
    method::Method
    reason::Symbol   # :insert or :delete
    invalidations::Invalidations
end

function countchildren(tree::InstanceTree)
    n = length(tree.children)
    for child in tree.children
        n += countchildren(child)
    end
    return n
end
countchildren(sigtree::Pair{<:Any,InstanceTree}) = countchildren(sigtree.second)

function countchildren(invalidations::Invalidations)
    n = 0
    for list in (invalidations.mt_backedges, invalidations.backedges)
        for tree in list
            n += countchildren(tree)
        end
    end
    return n
end

countchildren(methinv::MethodInvalidations) = countchildren(methinv.invalidations)

# We could use AbstractTrees here, but typically one is not interested in the full tree,
# just the top method and the number of children it has
function Base.show(io::IO, invalidations::Invalidations)
    iscompact = get(io, :compact, false)
    function showlist(io, treelist, indent=0)
        n = length(treelist)
        for (i, tree) in enumerate(treelist)
            if isa(tree, Pair)
                if isa(tree.first, Type)
                    print(io, "signature ", tree.first, " triggered ")
                elseif isa(tree.first, MethodInstance)
                    print(io, tree.first, " triggered ")
                end
                tree = tree.second
            end
            print(io, tree.mi, " (", countchildren(tree), " children)")
            if iscompact
                i < n && print(io, ", ")
            else
                print(io, '\n')
                i < n && print(io, " "^indent)
            end
        end
    end

    indent = iscompact ? "" : "   "
    for fn in (:mt_backedges, :backedges)
        val = getfield(invalidations, fn)
        if !isempty(val)
            print(io, indent, fn, ": ")
            showlist(io, val, length(indent)+length(String(fn))+2)
        end
        iscompact && print(io, "; ")
    end
    if !isempty(invalidations.tables)
        println(io, indent, length(invalidations.tables), " mt_cache")
    end
    iscompact && print(io, ';')
end

function Base.show(io::IO, methinv::MethodInvalidations)
    println(io, methinv.reason, " ", methinv.method, " invalidated:")
    show(io, methinv.invalidations)
end

# `list` is in RPN format, with the "reason" coming after the items
# Here is a brief summary of the cause and resulting entries
# delete_method:
#   [zero or more (mi, "invalidate_mt_cache") pairs..., zero or more (depth1 tree, loctag) pairs..., method, loctag] with loctag = "jl_method_table_disable"
# method insertion:
#   [zero or more (depth0 tree, sig) pairs..., same info as with delete_method except loctag = "jl_method_table_insert"]

# "invalidate_mt_cache" can alternatively be followed by
function invalidation_trees(list)
    function checkreason(reason, loctag)
        if loctag == "jl_method_table_disable"
            @assert reason === nothing || reason === :delete
            reason = :delete
        elseif loctag == "jl_method_table_insert"
            @assert reason === nothing || reason === :insert
            reason = :insert
        else
            error("unexpected reason ", loctag)
        end
        return reason
    end

    methodtrees = MethodInvalidations[]
    tree = nothing
    invalidations = Invalidations()
    reason = nothing
    i = 0
    while i < length(list)
        item = list[i+=1]
        if isa(item, MethodInstance)
            mi = item
            item = list[i+=1]
            if isa(item, Int32)
                depth = item
                if tree === nothing
                    tree = InstanceTree(mi)
                else
                    # Recurse back up the tree until we find the right parent
                    while tree.depth >= depth
                        tree = tree.parent
                    end
                    newtree = InstanceTree(mi, tree)
                    push!(tree.children, newtree)
                    tree = newtree
                end
            elseif isa(item, String)
                loctag = item
                if loctag == "invalidate_mt_cache"
                    push!(invalidations.tables, mi)
                    tree = nothing
                elseif loctag == "jl_method_table_insert"
                    push!(invalidations.backedges, mi=>getroot(tree))
                    tree = nothing
                else
                    error("unexpected loctag ", loctag)
                end
            else
                error("unexpected item ", item, " at ", i)
            end
        elseif isa(item, Method)
            method = item
            isassigned(list, i+1) || @show i
            item = list[i+=1]
            if isa(item, String)
                reason = checkreason(reason, item)
                push!(methodtrees, MethodInvalidations(method, reason, invalidations))
                invalidations = Invalidations()
                tree = nothing
            else
                error("unexpected item ", item, " at ", i)
            end
        elseif isa(item, String)
            # This shouldn't happen
            reason = checkreason(reason, item)
            push!(invalidations.backedges, getroot(tree))
            tree = nothing
        elseif isa(item, Type)
            push!(invalidations.mt_backedges, item=>getroot(tree))
            tree = nothing
        else
            error("unexpected item ", item, " at ", i)
        end
    end
    return sort(methodtrees; by=countchildren)
end

# function explain(methodtree::MethodInvalidations)
#     meth, invalidations = methodtree
#     if isa(meth, Method)
#         println("New method: ", meth)
#         println("Invalidated:")
#         for (sig, tree) in invalidations.instances
#             if isa(sig, Type)
#                 println("  signature ", sig, " as a backedge for ", tree.mi, ':')
#                 sigi = typeintersect(meth.sig, sig)
#                 println("    intersection: ", sigi)
#                 oldmeth = Base._methods_by_ftype(sig, -1, typemax(UInt))
#                 for ometh in oldmeth
#                     ometh = ometh[3]
#                     print("    matching method ", ometh)
#                     Base.isambiguous(ometh, meth; ambiguous_bottom=true) ? println(" (ambiguous)") : println()
#                 end
#             elseif sig === nothing
#                 println("    ", tree.mi)
#             end
#             println("  ", countchildren(tree), " direct and indirect descendants")
#         end
#         for tree in invalidations.tables
#             println("  method table for ", tree.mi)
#             println("    ", countchildren(tree), " direct and indirect descendants")
#         end
#     else
#         error("don't know what to do with ", meth)
#     end
# end

# function Base.findfirst(mi::MethodInstance, trees::Vector{InvalidationData})
#     for methodtree in trees
#         meth, invalidations = methodtree
#         mi == meth && return methodtree
#         for (i, inst) in enumerate(invalidations.instances)
#             idx = findfirst(mi, inst.second)
#             idx !== nothing && return Any[methodtree, :instances, i, idx...]
#         end
#         for (i, inst) in enumerate(invalidations.tables)
#             idx = findfirst(mi, inst)
#             idx !== nothing && return Any[methodtree, :tables, i, idx...]
#         end
#     end
#     return nothing
# end

# function Base.findfirst(mi::MethodInstance, tree::InstanceTree)
#     mi == tree.mi && return Int[]
#     for (i, child) in enumerate(tree.children)
#         ret = findfirst(mi, child)
#         if ret !== nothing
#             pushfirst!(ret, i)
#             return ret
#         end
#     end
#     return nothing
# end

macro snoopr(expr)
    quote
        local invalidations = ccall(:jl_debug_method_invalidation, Any, (Cint,), 1)
        Expr(:tryfinally,
            $(esc(expr)),
            ccall(:jl_debug_method_invalidation, Any, (Cint,), 0)
        )
        invalidations
    end
end
