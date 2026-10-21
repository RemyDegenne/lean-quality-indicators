namespace OAI

section

open Set Filter MeasureTheory Matrix

open scoped Topology ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator

namespace CAT0Fillings

lemma normalizedDet_bound {n : ℕ} (P : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hP : P.PosDef) (R : Fin n → Fin (n+1) → ℝ)
    (hR : ∀ i, Real.sqrt (R i ⬝ᵥ P⁻¹.mulVec (R i)) ≤ 1) (v : Euc (n+1)) :
    |normalizedDet P R v| ≤ ‖v‖ := by
  have h := abs_det_le_first_dual_norm (Matrix.vecCons (rawCovector P v) R) P hP hR
  change |Matrix.det (Matrix.vecCons (rawCovector P v) R)| ≤
    Real.sqrt (rawCovector P v ⬝ᵥ P⁻¹.mulVec (rawCovector P v))*Real.sqrt P.det at h
  rw [rawCovector_norm P hP] at h
  rw [normalizedDet,abs_div,abs_of_pos (Real.sqrt_pos.mpr hP.det_pos)]
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hP.det_pos)).mpr h

end CAT0Fillings
end
end OAI
