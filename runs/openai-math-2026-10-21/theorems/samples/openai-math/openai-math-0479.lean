namespace OAI

noncomputable section

namespace HyperbolicObstruction

open Set Metric

namespace SegmentChain

variable {X : Type*} [MetricSpace X] {N : ℕ} (hN : 0 < N)

include hN

variable (p : ℕ → X) (γ : ℕ → ℝ → X)
  (hg : ∀ i, i < N → IsSegment (γ i) (p i) (p (i+1)))

include hg

lemma curve_zero : curve hN p γ 0=p 0 := by
  let i : Fin N := ⟨0,hN⟩
  rw [curve_eq hN p γ hg i (by simp [i])]
  simpa [i] using (hg 0 hN).1

end SegmentChain
end HyperbolicObstruction
end
end OAI
