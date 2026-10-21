namespace OAI

noncomputable section

section

open Set Filter Topology MeasureTheory Matrix

open scoped ContDiff Matrix.Norms.Elementwise

namespace ThreeManifold.ReturningPassage

open Neck Cometric Turning ReturningCoefficients PassageDynamics SupportExtension

theorem truncated_return_nonnegative {right : Bool} {δ C b c : ℝ} {p : TVec}
    {t v : ℝ → ℝ} {V : ℝ → Vec} (hC : 18 ≤ C)
    (hδ : SmallParameter (3*C) (sourceMixed C) δ)
    (hbound : ∀ u ∈ Icc 0 1, ∀ q, sqnorm q/9 ≤ qform (coordinateCometric right δ u) q ∧
      qform (coordinateCometric right δ u) q ≤ 18*sqnorm q)
    (hder : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ e) ≤ C^2*δ^2)
    (hconc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    (hdom : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ p) ≤
      C*δ*qform (-deriv (deriv (coordinateCometric right δ)) u) p)
    (hc : c ∈ Ioo 0 b) (ht : ∀ s ∈ Icc 0 b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 b, HasDerivAt v (-force right δ p (t s)/2) s)
    (hta : ∀ s ∈ Icc 0 b, ContDiffAt ℝ ∞ t s)
    (hva : ∀ s ∈ Icc 0 b, ContDiffAt ℝ ∞ v s)
    (h0 : t 0 = 0) (hr : ∀ s ∈ Ioo 0 b, t s ∈ Ioo (0:ℝ) 1)
    (hvc : v c = 0) (hstar : 1/4 < t c)
    (henergy : ∀ s ∈ Icc 0 b, potential right δ p (t s) + v s^2 = 1)
    (hV : ∀ s ∈ Icc 0 b, ContDiffAt ℝ ∞ V s)
    (hcut : b < 2*c → V =ᶠ[𝓝 b] 0)
    (hfi : IntervalIntegrable (returnNormalDensity right δ p t v V (deriv V)) volume 0 b) :
    0 ≤ ∫ s in (0:ℝ)..b, returnNormalDensity right δ p t v V (deriv V) s := by
  have hb : 0 < b := hc.1.trans hc.2
  have hL : 0 < 2*c := by linarith [hc.1]
  have hd := reflected_closed_equations (force_smooth right δ p) hc ht hv hvc
  have hsmooth := reflected_closed_smooth (force_smooth right δ p) hc ht hv hvc hta hva
  have hcomplete := finite_turn_completion (force_smooth right δ p) hc ht hv hvc h0 hr
  simp only [sub_zero] at hd hsmooth hcomplete
  rcases hcomplete with ⟨hbL,het,hev,he0,heL,her⟩
  let te := reflectEven c t
  let ve := reflectOdd c v
  let W := if b < 2*c then cut b V else V
  have hWeq (s : ℝ) (hs : s ∈ Icc 0 b) : W s = V s := by
    dsimp only [W]
    split_ifs
    · exact cut_eq hs.2
    · rfl
  have hWdeq (s : ℝ) (hs : s ∈ Icc 0 b) : deriv W s = deriv V s := by
    dsimp only [W]
    split_ifs with hbl
    · exact cut_deriv (hcut hbl) hs.2
    · rfl
  have hWs (s : ℝ) (hs : s ∈ Icc 0 (2*c)) : ContDiffAt ℝ ∞ W s := by
    dsimp only [W]
    split_ifs with hbl
    · exact cut_smoothAt (hcut hbl) (fun hsb => hV s ⟨hs.1,hsb⟩)
    · exact hV s ⟨hs.1,hs.2.trans (le_of_not_gt hbl)⟩
  have hE (s : ℝ) (hs : s ∈ Icc 0 (2*c)) : potential right δ p (te s) + ve s^2 = 1 := by
    by_cases hsc : s ≤ c
    · simpa only [te,ve,reflectEven,reflectOdd,ite_eq_left hsc] using henergy s ⟨hs.1,hsc.trans hc.2.le⟩
    · have hh := henergy (2*c-s) ⟨by linarith [hs.2],by linarith [hc.2,lt_of_not_ge hsc]⟩
      simpa only [te,ve,reflectEven,reflectOdd,ite_eq_right hsc,neg_sq] using hh
  have hB := returning_arbitrary_field_nonnegative (right := right) (p := p) (t := te) (v := ve)
    hC hδ hbound hder hconc hdom hL
    (by simpa [te,reflectEven] using hstar)
    (fun s hs => (hd s hs).1) (fun s hs => (hd s hs).2)
    (fun s hs => (hsmooth s hs).1) (fun s hs => (hsmooth s hs).2)
    he0 heL her hE hWs
  let f := returnNormalDensity right δ p t v V (deriv V)
  let g := returnNormalDensity right δ p te ve W (deriv W)
  have heq : EqOn g f (Icc 0 b) := by
    intro s hs
    dsimp only [g,f,returnNormalDensity,momentumVelocity,te,ve]
    rw [het hs,hev hs,hWeq s hs,hWdeq s hs]
  have hzero : EqOn g 0 (Ioo b (2*c)) := by
    intro s hs
    have hbl : b < 2*c := hs.1.trans hs.2
    have hw : W = cut b V := ite_eq_left hbl
    dsimp only [g,returnNormalDensity]
    rw [hw,cut_zero hs.1,cut_deriv_zero hs.1,normalDensity_zero]
    rfl
  have hgi : IntervalIntegrable g volume 0 b := hfi.congr_uIoo (by
    rw [uIoo_of_le hb.le]; intro s hs; exact (heq (Ioo_subset_Icc_self hs)).symm)
  have hgib : IntervalIntegrable g volume b (2*c) := (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume b (2*c)).congr_uIoo (by
    rw [uIoo_of_le hbL]
    intro s hs
    exact (hzero hs).symm)
  have hgz : (∫ s in b..(2*c), g s) = 0 := by
    calc
      _ = ∫ s in b..(2*c), (0:ℝ) := intervalIntegral.integral_congr_Ioo_of_le hbL hzero
      _ = 0 := by simp
  have hgf : (∫ s in (0:ℝ)..b, g s) = ∫ s in (0:ℝ)..b, f s :=
    intervalIntegral.integral_congr (by simpa only [uIcc_of_le hb.le] using heq)
  have hi := intervalIntegral.integral_add_adjacent_intervals hgi hgib
  change (∫ s in (0:ℝ)..b, g s) + (∫ s in b..(2*c), g s) = (∫ s in (0:ℝ)..(2*c), g s) at hi
  rw [hgz,hgf,add_zero] at hi
  rw [hi]
  exact hB

end ThreeManifold.ReturningPassage
end
end
end OAI
