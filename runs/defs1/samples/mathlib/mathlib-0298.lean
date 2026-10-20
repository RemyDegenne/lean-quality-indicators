@[expose] public section

universe u

open CategoryTheory Limits

namespace Lattice

variable {T : Type u} (x₁ x₂ x₃ x₄ : T) [Lattice T]

/-- A bi-Cartesian square in a lattice consists of elements `x₁`, `x₂`, `x₃` and `x₄`
such that `x₂ ⊔ x₃ = x₄` and `x₂ ⊓ x₃ = x₁`. -/
structure BicartSq : Prop where
  sup_eq : x₂ ⊔ x₃ = x₄
  inf_eq : x₂ ⊓ x₃ = x₁

end Lattice
end
