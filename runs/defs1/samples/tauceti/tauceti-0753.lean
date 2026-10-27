public section

namespace TauCeti

universe u v w

open SimpleGraph

variable (k : Type w) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

/-- The public zigzag algebra of the one-vertex graph is the algebra of dual numbers. -/
noncomputable def zigzagAlgebraEquivA1 :
    zigzagAlgebra k (⊥ : SimpleGraph (Fin 1)) ≃ₐ[k] DualNumber k := by
  unfold zigzagAlgebra
  let A := fun C : (⊥ : SimpleGraph (Fin 1)).ConnectedComponent ↦
    zigzagComponentAlgebra k (⊥ : SimpleGraph (Fin 1)) C
  refine (algEquivPiUnique k A).trans <|
    (zigzagComponentAlgebraEquivULiftDualNumber k (⊥ : SimpleGraph (Fin 1)) default).trans ?_
  exact ULift.algEquiv (R := k) (A := DualNumber k)

end TauCeti
end
