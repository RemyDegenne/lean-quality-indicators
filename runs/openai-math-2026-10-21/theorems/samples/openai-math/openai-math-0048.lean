namespace OAI

namespace Yau.Geometry

open Yau.Jets Set Filter

open scoped ContDiff Topology

noncomputable section

lemma rescaledPhaseDefect_high_bound {U : Set Coord} (hU : IsOpen U)
    (phi : Coord → ℂ) (hp : ContDiffOn ℝ ∞ phi U) (L : Coord →L[ℝ] ℂ)
    {N s : ℝ} (hN : 1 ≤ N) (hs : 1 ≤ s) (x v : Coord)
    (hz : x+(N*s)⁻¹ • v ∈ U) {k : ℕ} (hk : 2 ≤ k) {C : ℝ}
    (hC : 0 ≤ C) (hb : ‖iteratedFDeriv ℝ k phi (x+(N*s)⁻¹ • v)‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (rescaledPhaseDefect phi L N s x) v‖ ≤ C/N := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hr := (rescaling_radius_bound hN hs).1
  let F : Coord → ℂ := fun z ↦ phi (x+(N*s)⁻¹ • z)
  have hF : ContDiffAt ℝ ∞ F v := (hp.contDiffAt (hU.mem_nhds hz)).comp v
    (contDiff_const.add (contDiff_id.const_smul _)).contDiffAt
  have hkle : (k:ℕ∞ω) ≤ ∞ := by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)
  have he : rescaledPhaseDefect phi L N s x =
      (fun z ↦ (N:ℂ) • (F z-phi x)) - (fun z ↦ (s⁻¹ • L) z) := rfl
  rw [he,iteratedFDeriv_sub_apply ((hF.sub contDiffAt_const).const_smul (N:ℂ) |>.of_le hkle)
    ((s⁻¹ • L).contDiff.contDiffAt.of_le hkle),iteratedFDeriv_linear_high _ _ hk,sub_zero,
    iteratedFDeriv_const_smul_apply' ((hF.sub contDiffAt_const).of_le hkle)]
  change ‖(N:ℂ) • iteratedFDeriv ℝ k (F - fun _ ↦ phi x) v‖ ≤ C/N
  rw [iteratedFDeriv_sub_apply (hF.of_le hkle) (contDiffAt_const.of_le hkle),
    iteratedFDeriv_const_of_ne (by omega : k ≠ 0)]
  simp only [Pi.zero_apply,sub_zero,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN0]
  have ha := affine_rescaling_derivative_power_on hU phi hp x v hr hz k
  calc
    _ ≤ N*(((N*s)⁻¹)^k*C) := mul_le_mul_of_nonneg_left
      (ha.trans (mul_le_mul_of_nonneg_left hb (by positivity))) hN0.le
    _ = (N*((N*s)⁻¹)^k)*C := by ring
    _ ≤ N⁻¹*C := mul_le_mul_of_nonneg_right (radius_high_power hN hs hk) hC
    _ = C/N := by ring

end
end Yau.Geometry
end OAI
