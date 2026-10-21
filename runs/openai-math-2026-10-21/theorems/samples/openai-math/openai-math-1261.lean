namespace OAI

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

namespace Percolation

universe u v

variable {V : Type u} {E : Type v}

section AnchoredPositionRows

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type*} [Fintype I]

theorem anchoredPositionKernel_eq_zero_off_ball (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) (x y : V)
    (hxy : y ∉ reachBall G x n) : anchoredPositionKernel G hloc γ n hdiam i j x y = 0 := by
  apply Finset.sum_eq_zero
  intro s hs
  apply ite_eq_right
  intro hy
  obtain ⟨⟨a,b,hab,rfl⟩,hx⟩ := (mem_segmentAnchors G hloc γ n hdiam i x s).mp hs
  change a (γ i) = x at hx
  change y = a (γ j) at hy
  exact hxy (by simpa only [hx,←hy] using mem_reachBall_aut G hab (hdiam i j))

end AnchoredPositionRows
end Percolation
end OAI
