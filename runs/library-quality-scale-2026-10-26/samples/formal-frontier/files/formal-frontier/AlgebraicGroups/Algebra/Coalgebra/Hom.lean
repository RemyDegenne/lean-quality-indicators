/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.CounitRange
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.RingTheory.Coalgebra.Hom

/-!
# Coalgebra homomorphism criteria

## Zero underlying maps

A coalgebra homomorphism has zero underlying linear map exactly when its source is
subsingleton. Counit preservation reduces this to the corresponding criterion for the
source counit. The scalar semiring, source and target may lie in independent universes.
Only the source needs the coalgebra laws; the target needs a coalgebra structure.

## Counit-determined morphisms

When the target counit is injective, coalgebra homomorphisms from a fixed source are
unique if they exist. Both endpoints need only coalgebra structures, and the scalar
semiring, source, target and morphism type may lie in independent universes.

* `CoalgHomClass.ext_of_injective_counit` gives equality of two morphisms.
* `CoalgHomClass.subsingleton_of_injective_counit` expresses at-most-one uniqueness
  without assuming existence.

## Counit kernels and injectivity

If the target counit is injective, the underlying linear map has the same kernel as
the source counit, and the homomorphism is injective exactly when the source counit is
injective. Source-counit injectivity alone implies injectivity of the homomorphism,
without an injectivity assumption on the target counit. These kernel and injectivity
criteria need only coalgebra structures on both modules, over a commutative semiring;
the scalar semiring, modules and morphism type may lie in four independent universes.

## References

Counit preservation and the bundled homomorphism API are supplied by
`Mathlib.RingTheory.Coalgebra.Hom`. The source criterion is
`Coalgebra.counit_eq_zero_iff` from `AlgebraicGroups.Algebra.Coalgebra.CounitRange`.
The reverse implication uses Mathlib's uniqueness of linear maps from a subsingleton
module in `Mathlib.Algebra.Module.LinearMap.Defs`. Counit-determined equality uses
function-like extensionality from `Mathlib.Data.FunLike.Basic`. The kernel criterion reuses
`LinearMap.ker_eq_bot_of_injective` and `LinearMap.ker_comp_of_ker_eq_bot` from
`Mathlib.Algebra.Module.Submodule.Ker`; the injectivity criteria reuse
`Function.Injective.of_comp` and `Function.Injective.of_comp_iff` from
`Mathlib.Logic.Function.Basic`.
-/

@[expose] public section

universe u v w uF

namespace CoalgHom

variable {R : Type u} {C : Type v} {C' : Type w}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid C'] [Module R C'] [CoalgebraStruct R C']

/-- The underlying linear map of a coalgebra homomorphism is zero exactly when its
source is subsingleton. Only a coalgebra structure is required on the target. -/
theorem toLinearMap_eq_zero_iff (f : C →ₗc[R] C') :
    f.toLinearMap = 0 ↔ Subsingleton C := by
  constructor
  · intro hf
    apply (Coalgebra.counit_eq_zero_iff R C).mp
    simpa only [hf, LinearMap.comp_zero] using f.counit_comp.symm
  · intro h
    have : Subsingleton C := h
    exact Subsingleton.elim _ _

end CoalgHom

namespace CoalgHomClass

variable {R : Type u} {A : Type v} {B : Type w} {F : Type uF}
  [CommSemiring R]
  [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B]
  [FunLike F A B] [CoalgHomClass F R A B]

include A

/-- Coalgebra homomorphisms are equal when the target counit is injective.
Only coalgebra structures, not coalgebra laws, are required on both endpoints. -/
theorem ext_of_injective_counit
    (hε : Function.Injective (Coalgebra.counit (R := R) (A := B) : B → R))
    (f g : F) : f = g :=
  DFunLike.ext f g fun x : A =>
    hε ((counit_comp_apply (R := R) f x).trans
      (counit_comp_apply (R := R) g x).symm)

/-- A type of coalgebra homomorphisms into a structure with injective counit has at most
one element. This asserts uniqueness only, not existence. -/
theorem subsingleton_of_injective_counit
    (hε : Function.Injective (Coalgebra.counit (R := R) (A := B) : B → R)) :
    Subsingleton F :=
  ⟨ext_of_injective_counit hε⟩

end CoalgHomClass

universe uR uA uB

namespace CoalgHomClass

variable {R : Type uR} {A : Type uA} {B : Type uB} {F : Type uF}
variable [CommSemiring R]
variable [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
variable [CoalgebraStruct R A] [CoalgebraStruct R B]
variable [FunLike F A B] [CoalgHomClass F R A B]

/-- If the target counit is injective, the underlying linear map of a coalgebra
homomorphism has the same kernel as the source counit. -/
theorem ker_eq_ker_counit (f : F)
    (hεB : Function.Injective (Coalgebra.counit (R := R) (A := B) : B → R)) :
    LinearMap.ker (LinearMap.ofClass f : A →ₗ[R] B) =
      LinearMap.ker (Coalgebra.counit (R := R) (A := A)) := by
  simpa only [counit_comp] using
    (LinearMap.ker_comp_of_ker_eq_bot (LinearMap.ofClass f : A →ₗ[R] B)
      (g := Coalgebra.counit (R := R) (A := B))
      (LinearMap.ker_eq_bot_of_injective hεB)).symm

/-- A coalgebra homomorphism is injective if its source counit is injective.
No injectivity assumption on the target counit is needed. -/
theorem injective_of_counit_injective (f : F)
    (hεA : Function.Injective (Coalgebra.counit (R := R) (A := A) : A → R)) :
    Function.Injective (f : A → B) := by
  apply Function.Injective.of_comp (f := (Coalgebra.counit (R := R) (A := B) : B → R))
  simpa only [Function.comp_def, counit_comp_apply] using hεA

/-- If the target counit is injective, a coalgebra homomorphism is injective exactly
when its source counit is injective. -/
theorem injective_iff_counit_injective (f : F)
    (hεB : Function.Injective (Coalgebra.counit (R := R) (A := B) : B → R)) :
    Function.Injective (f : A → B) ↔
      Function.Injective (Coalgebra.counit (R := R) (A := A) : A → R) := by
  rw [← funext (counit_comp_apply (R := R) f)]
  exact (Function.Injective.of_comp_iff hεB (f : A → B)).symm

end CoalgHomClass
