namespace OAI

section

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

variable {I : Type*} [Countable I]

theorem hot_regularity {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : ∀ i, Measurable (c₀ i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R)
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ F₀ p)
    (hF₀ : ∀ p, F₀ p ≤ R) (hSum₀ : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ u, F u = PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) u) :
    Measurable (hotForcing q b L T F c₀) ∧
      (∀ u, |hotForcing q b L T F c₀ u| ≤ HotApplication.realBound q*R^2+L*R) ∧
      Continuous (fun t => PhaseEssSup.size (fun p => hotRemainder q b L T F c₀ (t,p))) := by
  have hs := hotRemainder_solution hq hb hL hT hR hloss hFm hc₀m hF hc₀ hF₀ hSum₀ hFeq
  have hcm (i) := (coldLimit_solution hq hb hL hT hR hloss hFm (hc₀m i) hF (hc₀ i) hF₀ hFeq).1
  have hgm : Measurable (hotForcing q b L T F c₀) :=
    (measurable_forcing hFm q b L).sub
      (Measurable.tsum (fun i => measurable_coldForcing hFm (hcm i) q b L))
  have hg (u) : |hotForcing q b L T F c₀ u| ≤ HotApplication.realBound q*R^2+L*R := by
    rw [abs_of_nonneg (hs.2.2.1 u).1]
    apply (hs.2.2.1 u).2.trans
    exact (HotRepresentative.source_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (fun p => hF (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)).2
  have hr (u) : |hotRemainder q b L T F c₀ u| ≤ R := by
    rw [abs_of_nonneg (hs.2.1 u).1]
    exact (hs.2.1 u).2.trans (hF u).2
  refine ⟨hgm,hg,?_⟩
  apply PhaseEssSup.continuous_size hT hL _ hR hgm hs.1 hg hr hs.2.2.2
  unfold HotApplication.realBound
  positivity

end BoltzmannNonuniqueness.WeightedLocal
end
end
end OAI
