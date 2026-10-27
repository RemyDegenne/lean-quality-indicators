public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

section Retraction

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- The algebra homomorphism `kQ →ₐ[k] Π_k(Q)` sending a path of `Q` to the class of the same path
in the doubled quiver. -/
noncomputable def pathAlgebraToPreprojective : pathAlgebra k Q →ₐ[k] preprojectiveAlgebra k Q :=
  (preprojectiveMk k Q).comp (mapAlgHom k Symmetrify.of symmetrify_of_obj_bijective)

end Retraction
end TauCeti
end
