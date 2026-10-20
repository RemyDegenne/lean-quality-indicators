@[expose] public section

noncomputable section

namespace LocalInfiniteResidueExtension

universe u

open scoped Polynomial

variable (R : Type u) [CommRing R] [IsLocalRing R]

lemma infinite_residueField :
    Infinite (IsLocalRing.ResidueField (GenericLocalExtension R)) := by
  let _ : Infinite (RatFunc (IsLocalRing.maximalIdeal R).ResidueField) :=
    Infinite.of_injective
      (algebraMap (IsLocalRing.maximalIdeal R).ResidueField[X]
        (RatFunc (IsLocalRing.maximalIdeal R).ResidueField))
      (FaithfulSMul.algebraMap_injective
        (IsLocalRing.maximalIdeal R).ResidueField[X]
        (RatFunc (IsLocalRing.maximalIdeal R).ResidueField))
  exact (residueFieldEquivRatFunc R).toEquiv.infinite_iff.mpr inferInstance

end LocalInfiniteResidueExtension
end
end
