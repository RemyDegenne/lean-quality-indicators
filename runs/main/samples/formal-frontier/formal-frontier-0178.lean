@[expose] public section

universe u v

namespace Ideal

section LinearEquivalence

variable {R : Type u} {ι : Type v} [Ring R] [Finite ι]
  (I : ι → Ideal R) [∀ i, (I i).IsTwoSided]
  (hI : Pairwise (fun i j => I i ⊔ I j = ⊤))

theorem quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_span_singleton_mk_one :
    Submodule.span R
      {quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI
        (Quotient.mk (⨅ i, I i) (1 : R))} = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨r, hr⟩ := Quotient.mk_surjective
    ((quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI).symm x)
  apply Submodule.mem_span_singleton.mpr
  refine ⟨r, ?_⟩
  rw [← quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_smul]
  have hsmul : r • Quotient.mk (⨅ i, I i) (1 : R) =
      Quotient.mk (⨅ i, I i) r := by
    simpa only [smul_eq_mul, mul_one, Submodule.mkQ_apply, Quotient.mk_eq_mk] using
      ((⨅ i, I i).mkQ.map_smul r (1 : R)).symm
  rw [hsmul, hr, RingEquiv.apply_symm_apply]

end LinearEquivalence
end Ideal
end
