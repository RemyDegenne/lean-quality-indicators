public section

open scoped Manifold ContDiff Pointwise

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

namespace Diffeomorph

theorem fixingSubgroup_univ :
    fixingSubgroup (I := I) (M := M) (n := n) (Set.univ : Set M) = ⊥ := by
  exact TauCeti.fixingSubgroup_univ (G := M ≃ₘ^n⟮I, I⟯ M) (α := M)

end Diffeomorph
end
