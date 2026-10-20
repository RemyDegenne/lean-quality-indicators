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

theorem holomorphicSheafHom_app_ofHolomorphic [FiniteDimensional ℂ F]
    {D : Opens E} {G : Opens F} (f : D → G)
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f) (V : Opens G)
    (g : V → ℂ) (hg : MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ) g) :
    (holomorphicSheafHom f hf).hom.app (op V) (ofHolomorphic G V g hg) =
      ofHolomorphic D
        ((Opens.map (TopCat.ofHom ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V)
        (fun point ↦ g ⟨f point.1, point.2⟩)
        (holomorphic_precomp f hf V g hg) := by
  apply section_ext D _
  intro point
  exact holomorphicSheafHom_app_apply f hf V _ point

end ComplexManifold
end
end
