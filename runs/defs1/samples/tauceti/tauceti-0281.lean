public section

noncomputable section

namespace Module.Basis

variable {R A B C : Type*} [Semiring R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C} {κ σ : Type*}
  (hf : Function.Injective f) (hfg : Function.Exact f g)

variable {hf hfg}

variable (hf hfg)

/-- In a short exact sequence `0 → A → B → C → 0`, a basis `a` of `A`, a basis `c` of `C` and
lifts `s` of the vectors of `c` through `B → C` together form a basis of `B`, indexed by
`κ ⊕ σ`: the image of `a` on the left summand and the lifts `s` on the right summand. -/
def ofExactLift (a : Basis κ R A) (c : Basis σ R C) (s : σ → B) (hs : ∀ j, g (s j) = c j) :
    Basis (κ ⊕ σ) R B :=
  (a.prod c).map (exactLiftEquiv hf hfg c s hs).symm

end Module.Basis
end
end
