namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup

open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t m : ℕ)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)

theorem marked_phase_correction_coordinate_norm_le {p R : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p)
    (hmp : (m : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p)
    (hR : 1 ≤ R) (g z γ : D.RealGroup) (hg : g = z * γ)
    (hgphase : ‖torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord‖ ≤ 1 / 4)
    (hz : ‖(D.basis.baseChange ℝ).equivFun z.coord‖ ≤ R) :
    ‖(D.basis.baseChange ℝ).equivFun (realMarkedParameterDirection F v w marked t
      ((m : ℝ) • torusPhaseLinear (normalizedMarkedPhase F v w marked t m) γ.coord))‖ ≤
        2 * Real.exp (5 * p) * R := by
  let φ := normalizedMarkedPhase F v w marked t m
  have hsum : torusPhaseLinear φ g.coord = torusPhaseLinear φ z.coord + torusPhaseLinear φ γ.coord := by
    rw [hg, torusPhaseLinear_mul D]
  have hγ : torusPhaseLinear φ γ.coord = torusPhaseLinear φ g.coord - torusPhaseLinear φ z.coord := by
    rw [hsum, add_sub_cancel_left]
  have hzphase : ‖torusPhaseLinear φ z.coord‖ ≤ Real.exp (2 * p) * R :=
    (normalizedMarkedPhase_coordinate_norm_le F v w marked t m D.basis hd hphase z.coord).trans
      (mul_le_mul_of_nonneg_left hz (Real.exp_nonneg _))
  have hγnorm : ‖torusPhaseLinear φ γ.coord‖ ≤ 1 / 4 + Real.exp (2 * p) * R := by
    rw [hγ]
    exact (norm_sub_le _ _).trans (add_le_add hgphase hzphase)
  have hlarge : 1 ≤ Real.exp (2 * p) * R :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity)) hR
  have hγnorm' : ‖torusPhaseLinear φ γ.coord‖ ≤ 2 * Real.exp (2 * p) * R := by
    nlinarith
  have h := realMarkedParameterDirection_coordinate_norm_le F v w marked t D.basis ht hdir
    ((m : ℝ) • torusPhaseLinear φ γ.coord)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg m)] at h
  apply h.trans
  calc
    Real.exp (2 * p) * ((m : ℝ) * ‖torusPhaseLinear φ γ.coord‖) ≤
        Real.exp (2 * p) * (Real.exp p * (2 * Real.exp (2 * p) * R)) := by gcongr
    _ = 2 * Real.exp (5 * p) * R := by
      rw [show 5 * p = 2 * p + p + 2 * p by ring, Real.exp_add, Real.exp_add]
      ring

end Erdos3
end
end OAI
