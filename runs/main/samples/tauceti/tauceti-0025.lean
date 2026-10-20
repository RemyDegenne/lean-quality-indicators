public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V]

variable [DecidableEq (V → ℤ)]

theorem cubeVertices_nonempty (x : V → ℤ) (S : Finset V) :
    (cubeVertices x S).Nonempty :=
  ⟨x, base_mem_cubeVertices x S⟩

end PlumbingGraph
end TauCeti
end
