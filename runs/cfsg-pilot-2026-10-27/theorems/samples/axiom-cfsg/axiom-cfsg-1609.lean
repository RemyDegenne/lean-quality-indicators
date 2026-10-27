public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem centralConjugacyClassSum_one {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) : centralConjugacyClassSum ring (ConjClasses.mk (1 : group)) = 1 :=
  Subtype.ext conjugacyClassSum_one

end CFSG.TwoRankLowerBound.Helpers
end
