/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.Algebra.Ring.Equiv

/-!
# Opposite coefficients for right-linear forms

For a right module `M` over a possibly noncommutative semiring `R`, the forms
`M →ₗ[Rᵐᵒᵖ] R` carry pointwise left multiplication by `R`. Applying
`MulOpposite.op` to their values identifies them with `M →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ`.
This comparison is semilinear over `RingEquiv.opOp R`, not linear over an
identification of `R` with its opposite ring.

The additive equivalence and its inverse are Mathlib's
`LinearEquiv.arrowCongrAddEquiv` applied to the identity on `M` and
`MulOpposite.opLinearEquiv Rᵐᵒᵖ`. Scalar and module-carrier universes are
independent. Neither finite generation nor projectivity is needed here.

## References

* Mathlib contributors, revision `83abb3e776bdefcbc447a1e44d0debe4010039e5`:
  `LinearEquiv.arrowCongrAddEquiv`, `MulOpposite.opLinearEquiv`, the
  opposite-module actions, and `RingEquiv.opOp`.
* `ProjectiveModules.Dual.ModuleCat`, for the ordinary-carrier right dual
  and its canonical bundled restriction of scalars.
-/

@[expose] public section

universe uR uM uN

namespace LinearEquiv

variable (R : Type uR) [Semiring R]

section CoefficientComparison

-- These existing inverse-pair constructors are local to this section: no new
-- global inverse-pair or module instances are introduced.
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Change the values of a right-linear form from `R` to `Rᵐᵒᵖ` by `op`.
The pointwise scalar actions are related by the double-opposite ring
isomorphism. The inverse applies `unop` to each value. -/
def rightDualOpposite (M : Type uM) [AddCommMonoid M] [Module Rᵐᵒᵖ M] :
    LinearEquiv (RingEquiv.opOp R : R →+* Rᵐᵒᵖᵐᵒᵖ)
      (σ' := ((RingEquiv.opOp R).symm : Rᵐᵒᵖᵐᵒᵖ →+* R))
      (M →ₗ[Rᵐᵒᵖ] R) (M →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ) where
  toAddEquiv := LinearEquiv.arrowCongrAddEquiv (LinearEquiv.refl Rᵐᵒᵖ M)
    (MulOpposite.opLinearEquiv Rᵐᵒᵖ : R ≃ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ)
  map_smul' := by
    intro r f
    apply LinearMap.ext
    intro m
    rfl

/-- The coefficient comparison applies `op` to every value. -/
@[simp]
theorem rightDualOpposite_apply (M : Type uM)
    [AddCommMonoid M] [Module Rᵐᵒᵖ M] (f : M →ₗ[Rᵐᵒᵖ] R) (m : M) :
    rightDualOpposite R M f m = MulOpposite.op (f m) := rfl

/-- The inverse coefficient comparison applies `unop` to every value. -/
@[simp]
theorem rightDualOpposite_symm_apply (M : Type uM)
    [AddCommMonoid M] [Module Rᵐᵒᵖ M] (f : M →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ) (m : M) :
    (rightDualOpposite R M).symm f m = MulOpposite.unop (f m) := rfl

/-- Changing the coefficient carrier commutes with precomposition by a
right-linear map, with independent source and target carrier universes. -/
theorem rightDualOpposite_naturality (M : Type uM) (N : Type uN)
    [AddCommMonoid M] [AddCommMonoid N] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ N]
    (g : M →ₗ[Rᵐᵒᵖ] N) (f : N →ₗ[Rᵐᵒᵖ] R) :
    rightDualOpposite R M (f.comp g) =
      (rightDualOpposite R N f).comp g := by
  apply LinearMap.ext
  intro m
  simp only [rightDualOpposite_apply, LinearMap.comp_apply]

end CoefficientComparison

end LinearEquiv
