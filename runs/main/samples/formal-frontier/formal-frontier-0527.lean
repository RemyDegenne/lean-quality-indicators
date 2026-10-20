@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

theorem twoOpenSmallShortExact {X : TopCat.{u}} (U V : Opens X) :
    (twoOpenSmallShortComplex U V).ShortExact := by
  exact ShortComplex.shortExact_of_iso
    (twoOpenSmallToAmbientIso U V).symm
    (subcomplexUnionShortExact (TopCat.openSingularSet U)
      (TopCat.openSingularSet V))

end AlgebraicTopology
end
end
