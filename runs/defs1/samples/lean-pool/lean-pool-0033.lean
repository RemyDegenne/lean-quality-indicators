@[expose] public section

open Module

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

variable {V : Type*} [DecidableEq V]

open BigOperators

namespace SimpleGraph

section «Surjectivity»

namespace Tree

variable {X : Tree V} [∀ v, Fintype (X.neighborSet v)] (w : V → Aˣ) (f : V → M)

variable (v₀ : V)

section «Construction»

variable (n : ℕ) (g : X.edgeSet → M)

/-- The constructed preimage of a vertex function under the Laplacian. -/
def preimage (e : X.edgeSet) : M :=
  aux w f v₀ (X.dist v₀ (X.target v₀ e)) e

end «Construction»
end Tree
end «Surjectivity»
end SimpleGraph
end
