namespace OAI

section

namespace Erdos3.DilationBudget

open scoped TensorProduct NNReal

theorem niltest_complexity {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s n : ℕ} (Q : RationalFilteredNilmanifold L s n) {w : σ → ℕ} (T : Q.Niltest w)
    (t : ℕ) (q : ℤ) (d H : ℕ) (A : ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (hQ : Q.GeometryComplexityLE p) (hd : (d : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp (p + 1))
    (hA : (A : ℝ) ≤ Real.exp (reconstruction t q p))
    (hnorm : T.normBound = 1)
    (hlip : T.lipBound = rationalReconstructionLipschitzBound s d n H A 1) :
    T.ComplexityLE (total t q (MultilinearityBudget.reconstructionExponent s) p) := by
  have hR := reconstruction_bounds t q hp
  have hpR : p ≤ reconstruction t q p := (by linarith : p ≤ p + 1).trans hR.2
  have hTlip : (T.lipBound : ℝ) ≤ Real.exp
      ((reconstruction t q p + MultilinearityBudget.reconstructionExponent s) ^
        MultilinearityBudget.reconstructionExponent s) := by
    rw [hlip]
    exact MultilinearityBudget.reconstructionExponent_control s d n H A 1 _ hR.1
      (hd.trans hpR) (hQ.1.trans hpR) (hH.trans (Real.exp_le_exp.mpr hR.2)) hA
      (by simpa only [NNReal.coe_one] using Real.one_le_exp hR.1)
  have hpower : 0 ≤ (reconstruction t q p + MultilinearityBudget.reconstructionExponent s) ^
      MultilinearityBudget.reconstructionExponent s :=
    pow_nonneg (add_nonneg hR.1 (Nat.cast_nonneg _)) _
  have hlog := niltest_log_bound_of_exp T.normBound T.lipBound (a := 0) (by norm_num) hpower
    (by simp only [hnorm, NNReal.coe_one, Real.exp_zero, le_refl]) hTlip
  refine ⟨hQ.mono Q (total_bounds t q _ hp).1, ?_⟩
  have hlog' : Real.log (2 + (T.normBound : ℝ) + T.lipBound) ≤
      (reconstruction t q p + MultilinearityBudget.reconstructionExponent s) ^
        MultilinearityBudget.reconstructionExponent s + 4 := by
    simpa only [zero_add] using hlog
  exact hlog'.trans (total_bounds t q _ hp).2

end Erdos3.DilationBudget
end
end OAI
