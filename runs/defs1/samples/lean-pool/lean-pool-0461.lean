@[expose] public section

namespace Sabidussi

namespace LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)

/-- The incidence matrix as a linear map over `F₂`. -/
noncomputable def incidenceMap (F : Finset E) :
    (↑F → F₂) →ₗ[F₂] (↑(G.edgeSupport F) → F₂) :=
  (G.incidenceMatrix F).mulVecLin

end LoopMultigraph
end Sabidussi
end
