@[expose] public section

universe t u' u v' v w' w

namespace Representation

variable {k G H : Type*} [Semiring k] [Monoid G] [Monoid H] (φ : G →* H) {A B : Type*}
  [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B] (σ : Representation k G A)
  (ρ : Representation k G B)

@[simp]
lemma mem_coindV (f : H → A) : f ∈ coindV φ σ ↔ ∀ (g : G) (h : H), f (φ g * h) = σ g (f h) :=
  Iff.rfl

end Representation
end
