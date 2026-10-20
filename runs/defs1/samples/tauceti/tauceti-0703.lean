public section

noncomputable section

open scoped ENNReal

namespace lp

variable {𝕜 ι : Type*} [RCLike 𝕜]

variable (𝕜 ι)

/-- The isometric duality between bounded scalar families and the continuous dual of ℓ¹.
It sends `a` to the functional `x ↦ ∑' i, a i * x i`. -/
def dualOneEquiv : lp (fun _ : ι ↦ 𝕜) ∞ ≃ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) 1) := by
  classical
  have hmul : ‖ContinuousLinearMap.mul 𝕜 𝕜‖ ≤ ((1 : NNReal) : ℝ) := by
    simpa only [NNReal.coe_one] using ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜
  let P : lp (fun _ : ι ↦ 𝕜) ∞ →L[𝕜] StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) 1) :=
    dualPairing (𝕜 := 𝕜) ∞ 1 (fun _ : ι ↦ ContinuousLinearMap.mul 𝕜 𝕜)
      (fun _ ↦ hmul)
  have hP (a : lp (fun _ : ι ↦ 𝕜) ∞) (i : ι) (z : 𝕜) :
      P a (lp.single 1 i z) = a i * z := by
    simp only [P, dualPairing_apply, ContinuousLinearMap.mul_apply', lp.single_apply,
      Pi.single_apply, mul_ite, mul_zero, tsum_ite_eq]
  have hnorm (a : lp (fun _ : ι ↦ 𝕜) ∞) : ‖P a‖ = ‖a‖ := by
    apply le_antisymm
    · exact (P.le_opNorm a).trans (by
        simpa using mul_le_mul_of_nonneg_right
          (norm_dualPairing (p := ∞) (q := 1)
            (fun _ : ι ↦ ContinuousLinearMap.mul 𝕜 𝕜) (fun _ ↦ hmul)) (norm_nonneg a))
    · apply norm_le_of_forall_le (norm_nonneg _)
      intro i
      simpa [hP, lp.norm_single] using (P a).le_opNorm (lp.single 1 i (1 : 𝕜))
  refine LinearIsometryEquiv.ofSurjective
    { P.toLinearMap with norm_map' := hnorm } ?_
  intro f
  have hbound (i : ι) : ‖f (lp.single 1 i (1 : 𝕜))‖ ≤ ‖f‖ := by
    simpa [lp.norm_single] using f.le_opNorm (lp.single 1 i (1 : 𝕜))
  let a : lp (fun _ : ι ↦ 𝕜) ∞ :=
    ⟨fun i ↦ f (lp.single 1 i 1), memℓp_infty ⟨‖f‖, by
      rintro _ ⟨i, rfl⟩
      exact hbound i⟩⟩
  have ha (i : ι) : a i = f (lp.single 1 i 1) := rfl
  refine ⟨a, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  simp only [LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe, P, dualPairing_apply,
    ContinuousLinearMap.mul_apply', ha]
  exact (f.hasSum_lp_single_mul x).tsum_eq

end lp
end
end
