@[expose] public section

variable (R G V W U : Type*) [Monoid G] [Ring R] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V] [AddCommGroup W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [Module R W] [AddCommGroup U] [Module R U] [TopologicalSpace U]
  [IsTopologicalAddGroup U]

variable {R G V W U}

scoped[ContRepresentation] notation:30 π₁ " →ⁱL " π₂ =>
  ContIntertwiningMap π₁ π₂

namespace ContRepresentation

variable {H : Type*} [Monoid H]

variable {π : ContRepresentation R G V} {π' : ContRepresentation R H W}

variable {G H : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace R]
  [ContinuousSMul R V] [ContinuousSMul R W] [Group H] [TopologicalSpace H]
  (φ : G →ₜ* H) (π : ContRepresentation R G V)

variable [IsTopologicalGroup G] [IsTopologicalGroup H]

open ContinuousMap

section coind₁ResMap

variable [ContinuousSMul R U] {π' : ContRepresentation R H W} {π}

/-- Given a continuous group homomorphism `φ : H →ₜ* G`, a continuous intertwining map
`f : π.restrict φ →ⁱL π'` induces a continuous intertwining map
`π.coind₁.restrict φ →ⁱL π'.coind₁`, sending `F : C(G, V)` to `f ∘ F ∘ φ : C(H, W)`. -/
def coind₁ResMap (φ : H →ₜ* G) (f : π.restrict (φ : H →* G) →ⁱL π') :
    π.coind₁.restrict (φ : H →* G) →ⁱL π'.coind₁ :=
  (coind₁Map f).comp (coind₁Res φ π)

end coind₁ResMap
end ContRepresentation
end
