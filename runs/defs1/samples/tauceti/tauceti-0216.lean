public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

section Retraction

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- The algebra homomorphism `Π_k(Q) →ₐ[k] kQ` which fixes the vertex idempotents and the arrows of
`Q` and kills every formal reverse. It is the descent of
`TauCeti.PathAlgebra.symmetrifyRetraction` to the preprojective algebra. -/
noncomputable def preprojectiveToPathAlgebra : preprojectiveAlgebra k Q →ₐ[k] pathAlgebra k Q :=
  preprojectiveLift (symmetrifyRetraction k) (symmetrifyRetraction_preprojectiveRelator k Q)

end Retraction
end TauCeti
end
