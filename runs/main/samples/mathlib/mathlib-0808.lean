@[expose] public section

noncomputable section

open scoped LieGroup Manifold Derivation ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (G : Type*)
  [TopologicalSpace G] [ChartedSpace H G] [Monoid G] [ContMDiffMul I ∞ G] (g h : G)

variable {I G}

namespace LeftInvariantDerivation

variable {r : 𝕜} {X Y : LeftInvariantDerivation I G} {f f' : C^∞⟮I, G; 𝕜⟯}

variable (X Y f)

variable (r)

variable (I G)

variable {I G}

theorem left_invariant : 𝒅ₕ (smoothLeftMul_one I g) (evalAt (1 : G) X) = evalAt g X :=
  X.left_invariant'' g

end LeftInvariantDerivation
end
end
