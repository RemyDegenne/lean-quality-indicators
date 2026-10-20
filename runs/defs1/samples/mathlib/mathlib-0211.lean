@[expose] public noncomputable section

open CategoryTheory Finsupp

open scoped MonoidAlgebra

universe u v w

variable {k G : Type u} [CommRing k] {n : ℕ}

local notation "Gⁿ" => Fin n → G

set_option quotPrecheck false

local notation "Gⁿ⁺¹" => Fin (n + 1) → G

variable (G)

variable (k)

namespace Rep.standardComplex

open classifyingSpaceUniversalCover AlgebraicTopology CategoryTheory.Limits

variable {k G}

variable (k G) [Monoid G]

section Exactness

/-- The chain map from the standard resolution of `k` to `k[0]` given by `∑ nᵢgᵢ ↦ ∑ nᵢ` in
degree zero. -/
def εToSingle₀ :
    standardComplex k G ⟶ (ChainComplex.single₀ _).obj (Rep.trivial k G k) :=
  ((standardComplex k G).toSingle₀Equiv _).symm ⟨ε k G, d_comp_ε k G⟩

end Exactness
end Rep.standardComplex
end
