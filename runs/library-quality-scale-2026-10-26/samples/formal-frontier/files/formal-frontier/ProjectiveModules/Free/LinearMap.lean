/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import ProjectiveModules.Module.FiniteProjectiveHom

/-!
# Free and finite modules of linear maps

Let `M` be a finite free module over a semiring `A`, and let `N` carry commuting
`A`- and `S`-module structures. The module of `A`-linear maps from `M` to `N` is
`S`-free when `N` is `S`-free, and `S`-finite when `N` is `S`-finite. The first
conclusion does not require `N` to be finite. Finiteness is supplied by
`Module.Finite.linearMap_of_projective`, which only requires a finite projective
source and does not require `N` to be free. No `S`-action on the source is required.

The universal property `Basis.constr`, applied to `Module.Free.chooseBasis`,
identifies linear maps with families of target values indexed by the chosen
source basis, with independent universes for the scalar semiring and target
module. It is definitionally `Module.Free.constr` when that definition's
universes fit. Its inverse agrees with the factorization through the basis
representation, `Finsupp.lsum`, and evaluation of a scalar-linear map at `1`.
This equality holds over semirings and specializes to the factorization for
rings.

## References

* Mathlib, `Mathlib.LinearAlgebra.FreeModule.Basic` and
  `Mathlib.LinearAlgebra.FreeModule.Finite.Matrix`: Riccardo Brasca's
  formalization of free modules and free/finite linear-map modules, including
  the basis-representation, sum, and evaluation factorization.
* Mathlib, `Mathlib.LinearAlgebra.Basis.Defs`,
  `Mathlib.LinearAlgebra.Finsupp.LSum`, `Mathlib.LinearAlgebra.StdBasis`, and
  `Mathlib.RingTheory.Finiteness.Basic`: the basis universal property, sum
  equivalence, finite-product instances, and transport APIs used here.
-/

@[expose] public section

universe uA uS uM uN

variable (A : Type uA) (S : Type uS) (M : Type uM) (N : Type uN)

section BasisEvaluation

variable [Semiring A] [Semiring S]
variable [AddCommMonoid M] [Module A M] [Module.Free A M]
variable [AddCommMonoid N] [Module A N] [Module S N] [SMulCommClass A S N]

/-- The inverse of `Basis.constr` applied to `Module.Free.chooseBasis` evaluates
a linear map on the chosen basis. It agrees with changing the source by the
basis representation, restricting to each finitely supported coordinate, and
evaluating the resulting scalar-linear map at `1`. The chosen-basis universal
property is definitionally `Module.Free.constr` when that definition's
universes fit; over rings, its inverse is the usual free-module
factorization. -/
theorem Module.Free.constr_symm_eq_repr_congrLeft_lsum :
    ((Module.Free.chooseBasis A M).constr S).symm =
      (Module.Free.chooseBasis A M).repr.congrLeft N S ≪≫ₗ (Finsupp.lsum S).symm ≪≫ₗ
        LinearEquiv.piCongrRight (fun _ ↦ LinearMap.ringLmapEquivSelf A S N) := by
  ext f i
  simp [Finsupp.lsum_symm_apply]

end BasisEvaluation

section FiniteSource

variable [Semiring A] [Semiring S]
variable [AddCommMonoid M] [Module A M] [Module.Free A M] [Module.Finite A M]
variable [AddCommMonoid N] [Module A N] [Module S N] [SMulCommClass A S N]

/-- Linear maps from a finite free `A`-module to an `S`-free module form an
`S`-free module, provided the two actions on the target commute. The target
need not be finite. -/
instance (priority := 100) Module.Free.linearMap_of_finite [Module.Free S N] :
    Module.Free S (M →ₗ[A] N) := by
  let : Fintype (Module.Free.ChooseBasisIndex A M) :=
    Module.Free.ChooseBasisIndex.fintype A M
  exact Module.Free.of_equiv ((Module.Free.chooseBasis A M).constr S)

end FiniteSource
