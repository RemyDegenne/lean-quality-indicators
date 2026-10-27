public section

open scoped TensorProduct

namespace TauCeti

namespace GeneralLinear

open TrivSqZeroExt WithConv

attribute [local instance 100] LieRing.ofAssociativeRing

universe u w

noncomputable section

variable {R : Type u} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]

variable (n : ℕ)

local notation "H" => coordinateHopfAlgebra

/-- **The tangent Lie algebra of `GLₙ` is the matrix Lie algebra.** The underlying linear
equivalence evaluates tangent derivations on the generic coordinate entries, and the bracket on
matrices is the commutator. -/
noncomputable def tangentLieEquivMatrix :
    LieEquiv B
      (Derivation R (H (R := R) n)
        (Bialgebra.CounitAlgebra R (H (R := R) n) B))
      (Matrix (Fin n) (Fin n) B) where
  toFun := tangentMatrix n
  invFun := (tangentLinearEquivMatrix n).symm
  left_inv d := by
    rw [← tangentLinearEquivMatrix_apply]
    exact (tangentLinearEquivMatrix n).symm_apply_apply d
  right_inv X := by
    rw [← tangentLinearEquivMatrix_apply]
    exact (tangentLinearEquivMatrix n).apply_symm_apply X
  map_add' := map_add (tangentMatrix n)
  map_smul' b d := map_smul (tangentMatrix n) b d
  map_lie' := fun {d e} ↦ by
    exact tangentMatrix_lie n d e

end
end GeneralLinear
end TauCeti
end
