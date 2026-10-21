namespace OAI

noncomputable section

open Set Filter Topology MeasureTheory

open scoped RealInnerProductSpace

namespace EuclideanFiveColor

variable (c : ℂ → Fin 5) (hc : Measurable c)

lemma four_state_continuity (hw : WeakColoring 5 c)
    {x : ℕ → ℂ} {y : ℂ} (hx : ∀n,FourCenter c (x n)) (hy : FourCenter c y)
    (hxt : Tendsto x atTop (𝓝 y)) (s : Fin 3) :
    Tendsto (fun n => fourStateDistance c hc (x n) y s) atTop (𝓝 0) := by
  by_contra hn
  rw [Metric.tendsto_atTop] at hn
  push Not at hn
  obtain ⟨ε,hε,he⟩ := hn
  choose m hm using he
  have hmt : Tendsto m atTop atTop := tendsto_atTop_mono (fun n => (hm n).1) tendsto_id
  obtain ⟨φ,hφ,ht⟩ := four_state_subseq_continuity c hc hw (fun n => hx (m n)) hy (hxt.comp hmt)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (ht s) ε hε
  exact (hm (φ N)).2.not_gt (hN N le_rfl)

end EuclideanFiveColor
end
end OAI
