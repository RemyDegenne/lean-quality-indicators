@[expose] public section

universe u v

namespace Ideal

section Equivalence

variable {R : Type u} {ι : Type v} [Ring R] [Finite ι]
  (I : ι → Ideal R) [∀ i, (I i).IsTwoSided]
  (hI : Pairwise (fun i j => I i ⊔ I j = ⊤))

@[simp]
theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_symm_mk (r : R) :
    (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm
        (fun i => Quotient.mk (I i) r) =
      Quotient.mk (⨅ i, I i) r :=
  (quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm_apply_apply
    (Quotient.mk (⨅ i, I i) r)

end Equivalence
end Ideal
end
