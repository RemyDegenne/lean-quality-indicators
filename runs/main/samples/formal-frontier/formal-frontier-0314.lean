@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

open scoped ContDiff Manifold

universe u v w

namespace ComplexLine

@[simp] theorem ofHolomorphic_apply (D : Opens ℂ) (V : Opens D) (f : V → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (point : V) :
    ofHolomorphic D V f hf point = f point := rfl

end ComplexLine
end
end
