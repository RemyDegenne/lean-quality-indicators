@[expose] public section

open scoped ContDiff Manifold

open Set TopologicalSpace RS.Cech Module

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable (D : RS.Divisor X)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[elab_as_elim] theorem H1.induction_on {C : H1 D → Prop} (ξ : H1 D)
    (ih : ∀ (𝒰 : FinCover (⊤ : Opens X)) (c : H1Cover D 𝒰), C (toH1 D 𝒰 c)) : C ξ :=
  Module.DirectLimit.induction_on ξ ih

end RS.Cech
end
