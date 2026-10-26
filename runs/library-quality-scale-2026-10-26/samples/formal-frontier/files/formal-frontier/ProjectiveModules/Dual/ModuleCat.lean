/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.CategoryTheory.Opposites
public import ProjectiveModules.Category.FiniteProjective
public import ProjectiveModules.Module.RightDual

import ProjectiveModules.Module.FiniteProjectiveHom
import ProjectiveModules.Module.RightRegular

/-!
# The contravariant dual of right module categories

For a fixed, possibly noncommutative ring `R`, `ModuleCat.rightDual` sends a right
`R`-module `M` to the ordinary-carrier Hom `M →ₗ[Rᵐᵒᵖ] R`, regarded as a left
`R`-module. The codomain `R` has its canonical right regular action
`(MulOpposite.op a) • x = x * a`, and the left action on the Hom is pointwise:
`(r • f)(m) = r * f(m)`. These codomain actions commute by associativity, not
centrality. No left `R`-module structure on `M` is needed.

An opposite arrow acts by precomposition with its underlying right-linear map.
For each fixed arrow this is left `R`-linear; no left action on arbitrary spaces
of source morphisms is asserted. Scalar and module carrier universes are
independent, and the dual carrier inhabits their maximum.

The object, underlying-map, application and scalar lemmas expose the ordinary
Hom presentation. Identity and composition also have pointwise forms.

Restriction along `(RingEquiv.opOp R).symm.toRingHom` gives a canonical bundled
module over `Rᵐᵒᵖᵐᵒᵖ`. `rightDualRestrictScalarsEquiv` compares this object
with the forms valued in `Rᵐᵒᵖ`, by applying `op` to every value. This is the
same coefficient operator as `LinearEquiv.rightDualOpposite`, now linear over
the double-opposite ring. `isFiniteProjective_rightDual_restrictScalars` states
finite-projective closure for this bundled normalization; it uses the Hom
closure results of `ProjectiveModules.Module.FiniteProjectiveHom`, not a
whole-module-category equivalence or a new bidual construction.

## References

* Mathlib contributors, revision `83abb3e776bdefcbc447a1e44d0debe4010039e5`:
  the ordinary opposite-module action, commuting regular actions, pointwise Hom
  module, `LinearMap.lcomp`, and the `ModuleCat` morphism interface.
* `ProjectiveModules.Module.RightRegular`, for the existing ordinary-carrier
  right regular module convention.
* `ProjectiveModules.Module.RightDual`, for the semilinear coefficient
  comparison, built from Mathlib's additive Hom equivalence.
* `ProjectiveModules.Module.FiniteProjectiveHom`, for finite-projective Hom
  closure using Mathlib's finite-free splitting and retract APIs.
-/

@[expose] public section

universe uR uM

open CategoryTheory

namespace ModuleCat

variable (R : Type uR) [Ring R]

/-- The contravariant dual of right modules over a fixed ring. Its values are
ordinary right-linear maps into `R`, with the canonical pointwise left action,
and its morphisms are precomposition.

The definition is reducible so that elements of its values inherit the ordinary
`LinearMap` coercion to functions. -/
@[reducible, simps obj_carrier]
def rightDual :
    (ModuleCat.{uM} Rᵐᵒᵖ)ᵒᵖ ⥤ ModuleCat.{max uR uM} R where
  obj X := ModuleCat.of R (X.unop →ₗ[Rᵐᵒᵖ] R)
  map h := ModuleCat.ofHom (LinearMap.lcomp R R h.unop.hom)
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    rfl
  map_comp h k := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro z
    rfl

/-- The right dual object is exactly the ordinary-carrier right-linear Hom,
bundled with its pointwise left `R`-module structure. -/
theorem rightDual_obj (X : (ModuleCat.{uM} Rᵐᵒᵖ)ᵒᵖ) :
    (rightDual R).obj X = ModuleCat.of R (X.unop →ₗ[Rᵐᵒᵖ] R) := rfl

/-- The underlying linear map of the right dual functor is Mathlib's
left-linear precomposition map for the fixed opposite arrow. -/
theorem rightDual_map_hom {X Y : (ModuleCat.{uM} Rᵐᵒᵖ)ᵒᵖ} (h : X ⟶ Y) :
    ((rightDual R).map h).hom = LinearMap.lcomp R R h.unop.hom := rfl

/-- Applying a dual morphism and then evaluating is precomposition with the
underlying right-module morphism. -/
@[simp]
theorem rightDual_map_apply {X Y : (ModuleCat.{uM} Rᵐᵒᵖ)ᵒᵖ} (h : X ⟶ Y)
    (f : (rightDual R).obj X) (y : Y.unop) :
    (rightDual R).map h f y = f (h.unop y) :=
  LinearMap.lcomp_apply h.unop.hom f y

/-- The left action on the ordinary-carrier right dual multiplies the value
on the left. Right linearity in the source remains the inherited `map_smul` law. -/
theorem rightDual_smul_apply {X : (ModuleCat.{uM} Rᵐᵒᵖ)ᵒᵖ} (r : R)
    (f : (rightDual R).obj X) (m : X.unop) :
    (r • f) m = r * f m :=
  LinearMap.smul_apply r f m

/-- Precomposition and evaluation preserve the pointwise left scalar action. -/
theorem rightDual_map_smul_apply {X Y : (ModuleCat.{uM} Rᵐᵒᵖ)ᵒᵖ} (h : X ⟶ Y)
    (r : R) (f : (rightDual R).obj X) (y : Y.unop) :
    (rightDual R).map h (r • f) y = r * f (h.unop y) := by
  rw [rightDual_map_apply, rightDual_smul_apply]

/-- Identity precomposition fixes every value of a right-linear functional. -/
theorem rightDual_map_id_apply (X : (ModuleCat.{uM} Rᵐᵒᵖ)ᵒᵖ)
    (f : (rightDual R).obj X) (x : X.unop) :
    (rightDual R).map (𝟙 X) f x = f x := by
  rw [(rightDual R).map_id]
  rfl

/-- A composite of opposite arrows precomposes in the contravariant order:
the underlying map of the first arrow is evaluated after that of the second. -/
theorem rightDual_map_comp_apply {X Y Z : (ModuleCat.{uM} Rᵐᵒᵖ)ᵒᵖ}
    (h : X ⟶ Y) (k : Y ⟶ Z) (f : (rightDual R).obj X) (z : Z.unop) :
    (rightDual R).map (h ≫ k) f z = f (h.unop (k.unop z)) := by
  rw [(rightDual R).map_comp]
  rfl

section CoefficientComparison

-- The raw coefficient equivalence uses the canonical inverse ring homomorphisms.
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- The right dual restricted along the inverse double-opposite isomorphism
is linearly equivalent to the right-linear forms valued in `Rᵐᵒᵖ`. The
underlying additive operator and its inverse are those of
`LinearEquiv.rightDualOpposite`. -/
def rightDualRestrictScalarsEquiv (M : ModuleCat.{uM} Rᵐᵒᵖ) :
    ((ModuleCat.restrictScalars (RingEquiv.opOp R).symm.toRingHom).obj
      ((ModuleCat.rightDual R).obj (Opposite.op M))) ≃ₗ[Rᵐᵒᵖᵐᵒᵖ]
        (M →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ) where
  toAddEquiv := (LinearEquiv.rightDualOpposite R M).toAddEquiv
  map_smul' := by
    intro a f
    change LinearEquiv.rightDualOpposite R M
        ((RingEquiv.opOp R).symm a • (show M →ₗ[Rᵐᵒᵖ] R from f)) =
      a • LinearEquiv.rightDualOpposite R M (show M →ₗ[Rᵐᵒᵖ] R from f)
    simpa only [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] using
      (LinearEquiv.rightDualOpposite R M).map_smulₛₗ
        ((RingEquiv.opOp R).symm a) (show M →ₗ[Rᵐᵒᵖ] R from f)

/-- The bundled coefficient comparison applies `op` to every value. -/
@[simp]
theorem rightDualRestrictScalarsEquiv_apply (M : ModuleCat.{uM} Rᵐᵒᵖ)
    (f : (ModuleCat.restrictScalars (RingEquiv.opOp R).symm.toRingHom).obj
      ((ModuleCat.rightDual R).obj (Opposite.op M))) (m : M) :
    rightDualRestrictScalarsEquiv R M f m =
      MulOpposite.op ((show M →ₗ[Rᵐᵒᵖ] R from f) m) :=
  LinearEquiv.rightDualOpposite_apply R M (show M →ₗ[Rᵐᵒᵖ] R from f) m

/-- The inverse bundled coefficient comparison applies `unop` to every value. -/
@[simp]
theorem rightDualRestrictScalarsEquiv_symm_apply (M : ModuleCat.{uM} Rᵐᵒᵖ)
    (f : M →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ) (m : M) :
    (show M →ₗ[Rᵐᵒᵖ] R from (rightDualRestrictScalarsEquiv R M).symm f) m =
      MulOpposite.unop (f m) :=
  LinearEquiv.rightDualOpposite_symm_apply R M f m

/-- The canonical bundled comparison commutes with the restricted dual
morphism, which is precomposition by the original right-module morphism. -/
theorem rightDualRestrictScalarsEquiv_naturality
    {M N : ModuleCat.{uM} Rᵐᵒᵖ} (g : M ⟶ N)
    (f : (ModuleCat.restrictScalars (RingEquiv.opOp R).symm.toRingHom).obj
      ((ModuleCat.rightDual R).obj (Opposite.op N))) :
    rightDualRestrictScalarsEquiv R M
        ((ModuleCat.restrictScalars (RingEquiv.opOp R).symm.toRingHom).map
          ((ModuleCat.rightDual R).map g.op) f) =
      (rightDualRestrictScalarsEquiv R N f).comp g.hom := by
  exact LinearEquiv.rightDualOpposite_naturality R M N g.hom
    (show N →ₗ[Rᵐᵒᵖ] R from f)

/-- The canonically restricted right dual of a finite projective right module
is finite projective over the double-opposite ring. The coefficient comparison
reduces this closure to `Module.Finite.linearMap_of_projective` and
`Module.Projective.linearMap`. -/
theorem isFiniteProjective_rightDual_restrictScalars
    (M : ModuleCat.{uM} Rᵐᵒᵖ) (h : ModuleCat.isFiniteProjective Rᵐᵒᵖ M) :
    ModuleCat.isFiniteProjective Rᵐᵒᵖᵐᵒᵖ
      ((ModuleCat.restrictScalars (RingEquiv.opOp R).symm.toRingHom).obj
        ((ModuleCat.rightDual R).obj (Opposite.op M))) := by
  let : Module.Finite Rᵐᵒᵖ M := h.1
  let : Module.Projective Rᵐᵒᵖ M := h.2
  let : Module.Finite Rᵐᵒᵖᵐᵒᵖ (M →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ) :=
    Module.Finite.linearMap_of_projective Rᵐᵒᵖ Rᵐᵒᵖᵐᵒᵖ M Rᵐᵒᵖ
  let : Module.Projective Rᵐᵒᵖᵐᵒᵖ (M →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ) :=
    Module.Projective.linearMap Rᵐᵒᵖ Rᵐᵒᵖᵐᵒᵖ M Rᵐᵒᵖ
  exact ⟨Module.Finite.equiv (rightDualRestrictScalarsEquiv R M).symm,
    Module.Projective.of_equiv' (rightDualRestrictScalarsEquiv R M).symm⟩

end CoefficientComparison

end ModuleCat
