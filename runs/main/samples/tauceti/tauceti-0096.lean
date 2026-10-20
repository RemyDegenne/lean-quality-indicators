public section

noncomputable section

open Module

open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ}

namespace Foliation

variable [IsManifold I (n + 1) M]

variable [CompleteSpace 𝕜]

@[simp]
theorem ofSubmodule_distribution (S : Submodule 𝕜 E) [FiniteDimensional 𝕜 S] (hn : 1 ≤ n)
    (x : E) : (ofSubmodule S hn).distribution x = S :=
  (rfl)

end Foliation
end TauCeti
end
end
