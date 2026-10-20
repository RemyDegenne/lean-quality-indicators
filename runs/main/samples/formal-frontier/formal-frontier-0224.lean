@[expose] public section

universe u v

namespace Ideal

theorem quotientInfRingEquivPiQuotient_symm_apply_eq_mk_iff
    {R : Type u} {ι : Type v} [CommRing R] [Finite ι]
    (I : ι → Ideal R) (hI : Pairwise (fun i j => IsCoprime (I i) (I j)))
    (g : (i : ι) → R ⧸ I i) (r : R) :
    (quotientInfRingEquivPiQuotient I hI).symm g = Quotient.mk (⨅ i, I i) r ↔
      ∀ i, Quotient.mk (I i) r = g i := by
  rw [← quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_eq_quotientInfRingEquivPiQuotient
    I hI]
  exact quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_symm_apply_eq_mk_iff I _ g r

end Ideal
end
