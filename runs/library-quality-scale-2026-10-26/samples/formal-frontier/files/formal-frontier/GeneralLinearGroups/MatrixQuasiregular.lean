/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.QuasiregularIdeal
public import Mathlib.LinearAlgebra.Matrix.Ideal

/-!
# Quasi-regular ideals in matrix rings

This file proves that the entrywise matrix ideal of a quasi-regular two-sided
ideal is again quasi-regular. The proof passes through the Jacobson radical and
mathlib's matrix-Jacobson theorem.
-/

set_option warningAsError true

@[expose] public section

namespace TwoSidedIdeal

universe u v

variable {R : Type u} [Ring R]

/-- The entrywise matrix ideal of a quasi-regular two-sided ideal is
quasi-regular. The finite index type may be empty. -/
theorem IsQuasiregular.matrix {I : TwoSidedIdeal R} (hI : I.IsQuasiregular)
    (n : Type v) [Fintype n] [DecidableEq n] : (I.matrix n).IsQuasiregular := by
  have hScalar :
      (Ring.jacobson R).toTwoSided = (⊥ : TwoSidedIdeal R).jacobson := by
    ext x
    simp [TwoSidedIdeal.jacobson, Ideal.jacobson_bot]
  have hMatrix :
      ((Ring.jacobson R).toTwoSided).matrix n =
        (Ring.jacobson (Matrix n n R)).toTwoSided := by
    rw [hScalar, TwoSidedIdeal.matrix_jacobson_bot]
    ext X
    simp [TwoSidedIdeal.jacobson, Ideal.jacobson_bot]
  have hle :
      I.matrix n ≤ ((Ring.jacobson R).toTwoSided).matrix n :=
    TwoSidedIdeal.matrix_monotone n hI.le_ringJacobson
  intro X hX
  exact TwoSidedIdeal.ringJacobson_isQuasiregular X (hMatrix ▸ hle hX)

end TwoSidedIdeal
