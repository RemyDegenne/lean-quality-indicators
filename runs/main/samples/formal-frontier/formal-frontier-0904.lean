@[expose] public section

universe u v

namespace Ideal

section LinearEquivalence

variable {R : Type u} {ι : Type v} [Ring R] [Finite ι]
  (I : ι → Ideal R) [∀ i, (I i).IsTwoSided]
  (hI : Pairwise (fun i j => I i ⊔ I j = ⊤))

@[simp]
theorem quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop_toEquiv :
    (quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI).toEquiv =
      (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).toEquiv :=
  rfl

end LinearEquivalence
end Ideal
end
