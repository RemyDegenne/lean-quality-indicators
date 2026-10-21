namespace OAI

noncomputable section

open scoped RealInnerProductSpace Topology

namespace Problem358

namespace MaxPotential

variable {ι V : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem potential_le (y : ι → V) (c : ι → ℝ) (x : V) (a : ℝ)
    (h : ∀ i, ⟪x, y i⟫ + c i ≤ a) : potential y c x ≤ a := by
  exact Finset.sup'_le Finset.univ_nonempty _ (fun i _ => h i)

end MaxPotential
end Problem358
end
end OAI
