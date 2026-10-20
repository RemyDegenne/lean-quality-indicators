public section

open Multiplicative Topology

namespace TauCeti.Toric

variable {S : Type*} [AddCommMonoid S] {r r' : ℕ}

@[simp]
theorem monomialEmbedding_apply (g : AddGeneratingFamily S r)
    (x : AffineSemigroupComplexPoint S) (j : Fin r) :
    monomialEmbedding g x j = x (MonoidAlgebra.single (ofAdd (g.toFun j)) 1) := (rfl)

end TauCeti.Toric
end
