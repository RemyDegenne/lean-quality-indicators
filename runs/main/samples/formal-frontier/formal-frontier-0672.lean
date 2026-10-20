@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

open scoped ContDiff Manifold

universe u v w

namespace ComplexLine

theorem holomorphicSheafHom_app_ofHolomorphic {D E : Opens ℂ} (f : D → E)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (V : Opens E)
    (g : V → ℂ) (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) :
    (holomorphicSheafHom f hf).hom.app (op V) (ofHolomorphic E V g hg) =
      ofHolomorphic D
        ((Opens.map (TopCat.ofHom ⟨f, (holomorphic_contMDiff f hf).continuous⟩)).obj V)
        (fun point ↦ g ⟨f point.1, point.2⟩)
        (holomorphic_precomp f hf V g hg) := by
  apply section_ext D _
  intro point
  exact holomorphicSheafHom_app_apply f hf V _ point

end ComplexLine
end
end
