using SnoopCompile
using SnoopCompile: countchildren

function hastv(typ)
    isa(typ, UnionAll) && return true
    if isa(typ, DataType)
        for p in typ.parameters
            hastv(p) && return true
        end
    end
    return false
end

trees = invalidation_trees(@snoopr using DifferentialEquations)

function summary(trees)
    npartial = ngreater = nlesser = nambig = nequal = 0
    for methodtree in trees
        method = methodtree.method
        invs = methodtree.invalidations
        for fn in (:mt_backedges, :backedges)
            list = getfield(invs, fn)
            for (trigger, invtree) in list
                sig = isa(trigger, Core.MethodInstance) ? trigger.specTypes : trigger
                # if hastv(sig)
                #     npartial += countchildren(invtree)
                # else
                    ms1, ms2 = method.sig <: sig, sig <: method.sig
                    if ms1 && !ms2
                        ngreater += countchildren(invtree)
                    elseif ms2 && !ms1
                        nlesser += countchildren(invtree)
                    elseif ms1 && ms2
                        nequal += countchildren(invtree)
                    else
                        # if hastv(sig)
                        #     npartial += countchildren(invtree)
                        # else
                            nambig += countchildren(invtree)
                        # end
                    end
                # end
            end
        end
    end
    @assert nequal == 0
    println("$ngreater | $nlesser | $nambig |") # $npartial |")
end

summary(trees)
