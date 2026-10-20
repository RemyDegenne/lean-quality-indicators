public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Finsupp Simplicial

universe u

namespace TauCeti

variable {k : Type u} [Ring k]

variable (k)

variable {k}

variable (k)

variable {k}

section ModelChains

variable (k)

/-- The image, under the comparison with simplicial chains, of the identity cube of the model
`Iⁿ`. -/
def cubicalToSingularGen (n : ℕ) : ((singularChains k).obj (cubeModel.{u} n)).X n :=
  ((cubicalToSingular k).app (cubeModel.{u} n)).f n
    (NormalizedCubicalChain.ofCube (cubeModel.{u} n) k (upCube n))

end ModelChains
end TauCeti
end
end
