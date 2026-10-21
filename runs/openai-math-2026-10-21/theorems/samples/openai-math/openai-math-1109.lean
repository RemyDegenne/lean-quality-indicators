namespace OAI

noncomputable section

open MeasureTheory Filter Set Complex

open scoped Topology SchwartzMap FourierTransform Real

open scoped Topology

open MeasureTheory Set

open scoped ENNReal Topology

open Set Function Filter

open scoped Topology NNReal

open MeasureTheory Filter Set

open MeasureTheory Set Function

open scoped Topology ENNReal

open scoped Topology BigOperators

open MeasureTheory Set Filter

open scoped Topology FourierTransform

open MeasureTheory Set Filter Asymptotics

open MeasureTheory Set Filter Function

namespace ThreeTorus

open MeasureTheory Set Filter Function

open scoped Topology BigOperators FourierTransform

theorem quantile_fine_signal_estimate {w ρ : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : 0 ∉ tsupport w)
    (hwn : ∀ s, 0 ≤ w s)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, |ρ y| ≤ C/(1+y^2)) {D : ℝ}
    (hF : ∀ v, D < |v| → 𝓕 (fun y => (ρ y : ℂ)) v = 0)
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {g : UnitAddCircle → ℝ} (hg : Continuous g) {ε : ℝ}
    (hideal : ∀ s ∈ support w, ∀ y, |foldCircleDensity (scaledDensity ρ s) y-g y| ≤ ε)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, (∫ z,
      |foldCircleDensity (fineResidueKernel (passageBranchKernel (Ioo δ (1-δ)) (lawJitter ρ c)
        (fun p : ℝ × ℝ => w p.2*c.ψ p.1^2)) 1 0 n) z-
        foldCircleDensity w z*g ((n:ℤ) • z)| ∂AddCircle.haarAddCircle) <
      (∫ s, w s)*(4*δ+ε) + η := by
  have hq := (lawDensity_smooth c hρ hi).continuous
  have hqc := lawDensity_compact c hρ hi hp hm hδ hδ'
  have ht := realized_fold_signal_estimate hw hwc hw0 hwn hq hqc hρ.continuous hi hC hb hF
    hg hideal (fun _ => 0) hη
  have he : (∫ y, |lawDensity ρ c y-ρ y|) ≤ 4*δ := by
    simpa only [abs_sub_comm] using (lawDensity_error c hρ hi hp hm hδ hδ').2
  have hn : 0 ≤ ∫ s, w s := integral_nonneg hwn
  filter_upwards [ht] with n ht
  simp only [add_zero] at ht
  have heq : fineResidueKernel (passageBranchKernel (Ioo δ (1-δ)) (lawJitter ρ c)
      (fun p : ℝ × ℝ => w p.2*c.ψ p.1^2)) 1 0 n =
      fun s => w s*foldCircleDensity (scaledDensity (lawDensity ρ c) s) (((n:ℝ)*s:ℝ):UnitAddCircle) :=
    funext (lawJitter_fineKernel c hρ hi hp hm hδ w n)
  rw [heq]
  apply ht.trans_le
  nlinarith [mul_le_mul_of_nonneg_left he hn]

end ThreeTorus
end
end OAI
