public section

namespace TauCeti

open _root_.Quiver PathAlgebra MulOpposite

universe u v w

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

local notation "Π" => preprojectiveAlgebra k Q

local notation "π" => preprojectiveMk k Q

local notation "e" => fun i : Symmetrify Q => π (vertexIdempotent k i)

attribute [local instance] preprojectiveIntegerGradedAlgebra

/-- The internal grading on `e_i Π`, restricted from the actual preprojective algebra. -/
noncomputable def preprojectiveRightProjectiveGrading (i : Symmetrify Q) :
    InternalGrading k (preprojectiveRightProjective k i) :=
  (preprojectiveInternalGrading k (Q := Q)).submodule
    ((preprojectiveRightProjective k i).restrictScalars k)
    ((InternalGrading.isHomogeneous_ofDecomposition_piece_iff _ _).2
      (isHomogeneous_preprojectiveRightProjective k i))

end TauCeti
end
