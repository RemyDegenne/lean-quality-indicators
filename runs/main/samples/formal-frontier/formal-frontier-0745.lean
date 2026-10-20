@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

open scoped ContDiff Manifold

universe u v w

namespace ComplexManifold

local instance {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] : CompleteSpace V :=
  FiniteDimensional.complete ℂ V

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem holomorphicLocallyRingedSpaceMap_comp
    [FiniteDimensional ℂ F]
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {D : Opens E} {G : Opens F} {J : Opens H}
    (f : D → G) (g : G → J)
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f)
    (hg : MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ, H) g) :
    holomorphicLocallyRingedSpaceMap (g ∘ f) (hg.comp hf) =
      holomorphicLocallyRingedSpaceMap f hf ≫
        holomorphicLocallyRingedSpaceMap g hg := rfl

end ComplexManifold
end
end
