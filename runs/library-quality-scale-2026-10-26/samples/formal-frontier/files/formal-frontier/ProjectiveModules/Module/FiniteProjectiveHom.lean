/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Projective

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Linear maps from finite projective modules

Let `A` and `S` be semirings, let `M` be a finite projective `A`-module,
and let `N` carry commuting `A`- and `S`-module structures. The space
`M →ₗ[A] N` has its pointwise `S`-module structure:
`(s • f) m = s • f m`.

This module concerns two separate closure properties:

* `Module.Projective.linearMap`: projectivity of `N` over `S` gives
  projectivity of `M →ₗ[A] N` over `S`, without finiteness of `N` over `S`.
* `Module.Finite.linearMap_of_projective`: finiteness of `N` over `S` gives
  finiteness of `M →ₗ[A] N` over `S`, without projectivity of `N` over `S`.

No `S`-module structure on `M` is required. The scalar and carrier universes
are independent, and the linear-map carrier lies in `Type (max uM uN)`.

## Mathematical background

A finite projective module is a retract of a finite free module.
Precomposition makes its linear-map module a retract of the corresponding
finite product of copies of `N`. Projectivity and finiteness are preserved
by these retracts, separately.

## References

The finite-free splitting, finite-product and linear-map identifications,
and retract methods follow Mathlib's formalization in
`Mathlib.RingTheory.Finiteness.Projective`,
`Mathlib.LinearAlgebra.Pi`, `Mathlib.LinearAlgebra.BilinearMap`,
`Mathlib.Algebra.Module.Projective`, and `Mathlib.RingTheory.Finiteness.Basic`.
-/

@[expose] public section

universe uA uS uM uN

/-- Linear maps from a finite projective `A`-module to a projective `S`-module
form a projective `S`-module, when the two actions on the target commute.
The `S`-action is pointwise; no finiteness over `S` is required of the target.
The finite-free splitting, finite-product Hom identification and projective
retract argument follow Mathlib's projective-module formalization. -/
theorem Module.Projective.linearMap
    (A : Type uA) (S : Type uS) (M : Type uM) (N : Type uN)
    [Semiring A] [Semiring S]
    [AddCommMonoid M] [AddCommMonoid N]
    [Module A M] [Module A N] [Module S N] [SMulCommClass A S N]
    [Module.Finite A M] [Module.Projective A M]
    [Module.Projective S N] :
    Module.Projective S (M →ₗ[A] N) := by
  obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  -- Precomposition reverses the maps in the finite-free splitting.
  have hsplit : (LinearMap.lcomp S N g).comp (LinearMap.lcomp S N f) = LinearMap.id := by
    ext h m
    simpa only [LinearMap.comp_apply, LinearMap.lcomp_apply, LinearMap.id_apply] using
      congrArg h (DFunLike.congr_fun hfg m)
  have : Module.Projective S (Fin n → N) :=
    Module.Projective.of_equiv'
      (DFinsupp.linearEquivFunOnFintype (R := S) (M := fun _ : Fin n => N))
  have : Module.Projective S ((Fin n → A) →ₗ[A] N) :=
    Module.Projective.of_equiv' (LinearEquiv.piRing A N (Fin n) S).symm
  exact Module.Projective.of_split (LinearMap.lcomp S N f) (LinearMap.lcomp S N g) hsplit

/-- Linear maps from a finite projective `A`-module to a finite `S`-module
form a finite `S`-module, when the two actions on the target commute.
The `S`-action is pointwise; no projectivity over `S` is required of the target.
The finite-free splitting, finite-product Hom identification and finite
retract argument follow Mathlib's finitely generated module formalization. -/
instance (priority := 100) Module.Finite.linearMap_of_projective
    (A : Type uA) (S : Type uS) (M : Type uM) (N : Type uN)
    [Semiring A] [Semiring S]
    [AddCommMonoid M] [AddCommMonoid N]
    [Module A M] [Module A N] [Module S N] [SMulCommClass A S N]
    [Module.Finite A M] [Module.Projective A M]
    [Module.Finite S N] :
    Module.Finite S (M →ₗ[A] N) := by
  obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  have hsplit : (LinearMap.lcomp S N g).comp (LinearMap.lcomp S N f) = LinearMap.id := by
    ext h m
    simpa only [LinearMap.comp_apply, LinearMap.lcomp_apply, LinearMap.id_apply] using
      congrArg h (DFunLike.congr_fun hfg m)
  have : Module.Finite S (Fin n → N) := inferInstance
  have : Module.Finite S ((Fin n → A) →ₗ[A] N) :=
    Module.Finite.equiv (LinearEquiv.piRing A N (Fin n) S).symm
  exact Module.Finite.of_surjective (LinearMap.lcomp S N g)
    (LinearMap.surjective_of_comp_eq_id (LinearMap.lcomp S N f) (LinearMap.lcomp S N g)
      hsplit)
