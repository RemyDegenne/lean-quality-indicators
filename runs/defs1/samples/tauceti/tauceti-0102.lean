public section

namespace TauCeti

namespace Sym

variable {α : Type*} {n : ℕ} {A B : Fin n → Set α}

/-- The unordered `n`-tuples having one point in each member of a family `A : Fin n → Set α` of
subsets, presented as the range of the parametrization by ordered tuples.

For the `g` attaching curves `α₁, …, α_g` of a Heegaard diagram on a surface `Σ` this is the torus
`T_α ⊆ Sym^g(Σ)`; the name follows `Set.pi`, of which it is the unordered analogue. -/
def pi (A : Fin n → Set α) : Set (Sym α n) :=
  Set.range fun x : ∀ i, ↥(A i) => ofFn fun i => (x i : α)

end Sym
end TauCeti
end
