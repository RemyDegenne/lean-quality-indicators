/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Category.FiniteProjective
public import ProjectiveModules.Category.SubmoduleEquivalence
public import ProjectiveModules.Module.Injective
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import ProjectiveModules.Order.CompactlyGenerated

/-!
# Finite generation, presentation and projectivity under module-category equivalences

A given equivalence of module categories preserves and reflects finite generation.
The scalar and carrier universes may be independent. It also preserves finite
presentation and finite projectivity when the target carrier universe is
`max uS vS`, and reflects these properties when both carrier universes have this
form. The forward theorems place no such restriction on the source carrier universe.
Self-injectivity of the regular modules is also preserved and reflected when both
carrier universes have the corresponding form.

## Main results

* `ModuleCat.finite_iff_of_equivalence`
* `ModuleCat.finitePresentation_of_equivalence`
* `ModuleCat.finitePresentation_iff_of_equivalence`
* `ModuleCat.isFiniteProjective_of_equivalence`
* `ModuleCat.isFiniteProjective_iff_of_equivalence`
* `ModuleCat.selfInjective_iff_of_equivalence`

The conclusions use `Module.Finite`, `Module.FinitePresentation` and the existing
`ModuleCat.isFiniteProjective` property defining `ModuleCat.FiniteProjective`.
The lemmas `ModuleCat.isFG_iff` and `ModuleCat.isFiniteProjective_iff` give the
corresponding object-property and algebraic formulations. No linearity of the
functor, commutativity of the rings or freeness of the modules is assumed.

Finite presentation below means finite generation together with finitely generated
relations, using `Module.FinitePresentation`. It is preserved when the target
carrier universe is `max uS vS`, and preserved and reflected when both carrier
universes have the corresponding form. These are standard sufficient universe
bounds, not necessary conditions for every equivalence.

## Implementation notes

The equivalence induces an order isomorphism on submodule lattices via
`ModuleCat.subobjectModule`. Finite generation is compactness of the greatest
submodule. Projectivity passes through categorical projectivity; the local
`small_max` instance is used only to return to algebraic projectivity. Finite
presentation is transported using a finite free cover in the target category:
its inverse image has a finitely generated kernel, and equivalences preserve
kernels and finite generation. All statements assume a given equivalence; they
do not assert its existence.

For self-injectivity, the inverse image of the lifted target regular module is
finite projective, hence injective over a self-injective source ring. Categorical
injectivity passes through the equivalence, and its counit identifies the result
with the lifted target regular module. Injectivity then descends from the lift.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, for Morita
  invariance of finite projective modules.
* Mathlib's module-category and subobject formalizations by Markus Himmel,
  Bhavik Mehta and Kim Morrison, and its categorical projectivity formalization
  by Markus Himmel and Kim Morrison.
* Mathlib's finiteness formalization by Johan Commelin, for the
  compact-submodule characterization. The order-theoretic transport uses
  `ProjectiveModules.Order.CompactlyGenerated` and the Mathlib APIs credited there.
* Mathlib's finite-presentation and kernel criteria for modules by Andrew Yang.
* The finite-projective object property and category by Formal Frontier Agents.
* Mathlib's algebraic and categorical injectivity formalizations by Jujian Zhang
  and Kevin Buzzard.
-/

@[expose] public section

universe uR uS vR vS

open CategoryTheory

section Finiteness

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]

namespace ModuleCat

/-- An equivalence of module categories preserves and reflects finite generation,
with independent scalar and carrier universes.

This is the finite-generation component of Morita invariance; see C. A. Weibel,
*The K-book: An Introduction to Algebraic K-theory*. -/
theorem finite_iff_of_equivalence
    (e : ModuleCat.{vR} R ≌ ModuleCat.{vS} S) (X : ModuleCat.{vR} R) :
    Module.Finite S (e.functor.obj X) ↔ Module.Finite R X := by
  -- Every subobject is represented by a submodule, with no smallness of the ring.
  let φ : Submodule R X ≃o Submodule S (e.functor.obj X) :=
    submoduleOrderIsoOfEquivalence e X
  -- Finite generation means compactness of the greatest submodule.
  simp only [Module.finite_def, Submodule.fg_iff_compact]
  simpa only [φ.map_top] using φ.isCompactElement_iff (⊤ : Submodule R X)

end ModuleCat

end Finiteness

section FiniteProjectivity

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]

namespace ModuleCat

/-- An equivalence of module categories sends finite projective modules to finite
projective modules when the target carrier universe contains the target ring.

This is the forward finite-projective part of Morita invariance; see C. A. Weibel,
*The K-book: An Introduction to Algebraic K-theory*. -/
theorem isFiniteProjective_of_equivalence
    (e : ModuleCat.{vR} R ≌ ModuleCat.{max uS vS} S) (X : ModuleCat.{vR} R) :
    ModuleCat.isFiniteProjective R X →
      ModuleCat.isFiniteProjective S (e.functor.obj X) := by
  intro hX
  obtain ⟨hfin, hproj⟩ := (isFiniteProjective_iff X).mp hX
  let : Module.Finite R X := hfin
  let : Module.Projective R X := hproj
  -- Algebraic projectivity gives categorical projectivity at any source height.
  let : CategoryTheory.Projective X :=
    projective_of_categoryTheory_projective X
  let : CategoryTheory.Projective (e.functor.obj X) :=
    (e.map_projective_iff X).mpr inferInstance
  -- Only the return to algebraic projectivity needs the supported target height.
  let : Small.{max uS vS} S := small_max S
  exact (isFiniteProjective_iff (e.functor.obj X)).mpr
    ⟨(finite_iff_of_equivalence R S e X).mpr inferInstance,
      projective_of_module_projective (e.functor.obj X)⟩

/-- An equivalence of module categories preserves and reflects finite projectivity
when each carrier universe contains its scalar-ring universe.

This is the finite-projective part of Morita invariance; see C. A. Weibel,
*The K-book: An Introduction to Algebraic K-theory*. -/
theorem isFiniteProjective_iff_of_equivalence
    (e : ModuleCat.{max uR vR} R ≌ ModuleCat.{max uS vS} S)
    (X : ModuleCat.{max uR vR} R) :
    ModuleCat.isFiniteProjective S (e.functor.obj X) ↔
      ModuleCat.isFiniteProjective R X := by
  constructor
  · intro hY
    obtain ⟨hfin, hproj⟩ := (isFiniteProjective_iff (e.functor.obj X)).mp hY
    let : Module.Finite S (e.functor.obj X) := hfin
    let : Module.Projective S (e.functor.obj X) := hproj
    let : CategoryTheory.Projective (e.functor.obj X) :=
      projective_of_categoryTheory_projective (e.functor.obj X)
    -- Reflection uses the given equivalence, not an enlarged or chosen equivalence.
    let : CategoryTheory.Projective X :=
      (e.map_projective_iff X).mp inferInstance
    let : Small.{max uR vR} R := small_max R
    exact (isFiniteProjective_iff X).mpr
      ⟨(finite_iff_of_equivalence R S e X).mp inferInstance,
        projective_of_module_projective X⟩
  · exact isFiniteProjective_of_equivalence R S e X

end ModuleCat

end FiniteProjectivity

section FinitePresentation

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]

namespace ModuleCat

/-- An equivalence of module categories sends finitely presented modules to
finitely presented modules when the target carrier universe contains its
scalar-ring universe.

Here finite presentation is `Module.FinitePresentation`: finite generation
with finitely generated relations. Scalar and carrier universes are independent,
and the source carrier universe is unrestricted. The displayed target universe
is a standard sufficient choice, not a necessary condition for every equivalence. -/
theorem finitePresentation_of_equivalence
    (e : ModuleCat.{vR} R ≌ ModuleCat.{max uS vS} S) (X : ModuleCat.{vR} R) :
    Module.FinitePresentation R X →
      Module.FinitePresentation S (e.functor.obj X) := by
  intro hX
  letI : Module.FinitePresentation R X := hX
  letI : Module.Finite S (e.functor.obj X) :=
    (finite_iff_of_equivalence R S e X).mpr inferInstance
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' S (e.functor.obj X)
  -- The target height contains a finite free cover, without changing the source height.
  let P : ModuleCat.{max uS vS} S := of S (ULift.{vS} (Fin n → S))
  let liftEquiv : P ≃ₗ[S] (Fin n → S) := ULift.moduleEquiv
  let p : P ⟶ e.functor.obj X := ofHom (f.comp liftEquiv.toLinearMap)
  have hp : Function.Surjective p.hom := hf.comp liftEquiv.surjective
  letI : Epi p := (epi_iff_surjective p).mpr hp
  letI : Module.FinitePresentation S P :=
    Module.FinitePresentation.of_equiv liftEquiv.symm
  let q : e.inverse.obj P ⟶ e.inverse.obj (e.functor.obj X) := e.inverse.map p
  letI : Module.Finite R (e.inverse.obj P) :=
    (finite_iff_of_equivalence S R e.symm P).mpr inferInstance
  let unitEquiv : X ≃ₗ[R] e.inverse.obj (e.functor.obj X) :=
    (e.unitIso.app X).toLinearEquiv
  letI : Module.FinitePresentation R (e.inverse.obj (e.functor.obj X)) :=
    Module.FinitePresentation.of_equiv unitEquiv
  have hq : Function.Surjective q.hom := (epi_iff_surjective q).mp inferInstance
  have hkerq : q.hom.ker.FG := Module.FinitePresentation.fg_ker q.hom hq
  -- Concrete kernels exist at the original carrier height, even for a larger ring.
  letI : Limits.HasKernels (ModuleCat.{vR} R) := hasKernels_moduleCat
  letI : Limits.HasKernels (ModuleCat.{max uS vS} S) := hasKernels_moduleCat
  letI : Module.Finite R q.hom.ker := Module.Finite.iff_fg.mpr hkerq
  letI : Module.Finite R (Limits.kernel q : ModuleCat.{vR} R) :=
    Module.Finite.equiv (kernelIsoKer q).toLinearEquiv.symm
  letI : Module.Finite S (e.functor.obj (Limits.kernel q)) :=
    (finite_iff_of_equivalence R S e (Limits.kernel q)).mpr inferInstance
  -- Kernel preservation followed by counit naturality identifies this with ker p.
  let i : e.functor.obj (Limits.kernel q) ≅ of S p.hom.ker :=
    Limits.PreservesKernel.iso e.functor q ≪≫
      Limits.kernel.mapIso (e.functor.map q) p (e.counitIso.app P)
        (e.counitIso.app (e.functor.obj X)) (by
          simpa only [q, Functor.comp_map, Functor.id_map, Iso.app_hom] using
            e.counitIso.hom.naturality p) ≪≫
      kernelIsoKer p
  have hkerp : p.hom.ker.FG :=
    Module.Finite.iff_fg.mp (Module.Finite.equiv i.toLinearEquiv)
  exact Module.finitePresentation_of_surjective p.hom hp hkerp

/-- An equivalence of module categories preserves and reflects finite presentation
when each carrier universe contains its scalar-ring universe.

Finite presentation is `Module.FinitePresentation`: finite generation with
finitely generated relations. Scalar and carrier universes are independent.
The displayed universe choices are standard sufficient bounds; no necessity for
individual rings or equivalences is asserted. -/
theorem finitePresentation_iff_of_equivalence
    (e : ModuleCat.{max uR vR} R ≌ ModuleCat.{max uS vS} S)
    (X : ModuleCat.{max uR vR} R) :
    Module.FinitePresentation S (e.functor.obj X) ↔
      Module.FinitePresentation R X := by
  constructor
  · intro hX
    letI : Module.FinitePresentation R (e.inverse.obj (e.functor.obj X)) :=
      finitePresentation_of_equivalence S R e.symm (e.functor.obj X) hX
    let unitEquiv : e.inverse.obj (e.functor.obj X) ≃ₗ[R] X :=
      (e.unitIso.app X).toLinearEquiv.symm
    exact Module.FinitePresentation.of_equiv unitEquiv
  · exact finitePresentation_of_equivalence R S e X

end ModuleCat

end FinitePresentation

section SelfInjectivity

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]

namespace ModuleCat

private theorem selfInjective_of_equivalence
    (e : ModuleCat.{max uR vR} R ≌ ModuleCat.{max uS vS} S)
    [Module.Injective R R] : Module.Injective S S := by
  -- Use the target regular module at the target carrier height.
  let Y : ModuleCat.{max uS vS} S := of S (ULift.{vS} S)
  have hY : isFiniteProjective S Y :=
    (isFiniteProjective_iff Y).mpr ⟨inferInstance, inferInstance⟩
  have hX : Module.Finite R (e.inverse.obj Y) ∧
      Module.Projective R (e.inverse.obj Y) :=
    (isFiniteProjective_iff (e.inverse.obj Y)).mp
      (isFiniteProjective_of_equivalence S R e.symm Y hY)
  let : Module.Finite R (e.inverse.obj Y) := hX.1
  let : Module.Projective R (e.inverse.obj Y) := hX.2
  let : Module.Injective R (e.inverse.obj Y) :=
    Module.injective_of_finite_projective R (e.inverse.obj Y)
  let : CategoryTheory.Injective (e.inverse.obj Y) :=
    Module.injective_object_of_injective_module R (e.inverse.obj Y)
  have hImage : CategoryTheory.Injective (e.functor.obj (e.inverse.obj Y)) :=
    (e.map_injective_iff (e.inverse.obj Y)).mpr inferInstance
  -- The counit, not an identification of the two regular modules, is the comparison.
  let : CategoryTheory.Injective Y :=
    CategoryTheory.Injective.of_iso (e.counitIso.app Y) hImage
  exact Module.injective_of_ulift_injective S
    (Module.injective_module_of_injective_object S Y)

/-- Self-injectivity of the regular module is invariant under an equivalence of
module categories, with independent scalar and carrier universes.

The proof uses the finite projective inverse image of the lifted target regular
module and the counit of the given equivalence. It does not identify the image of
one regular module with the other. This is Morita invariance of self-injectivity;
see C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*. -/
theorem selfInjective_iff_of_equivalence
    (e : ModuleCat.{max uR vR} R ≌ ModuleCat.{max uS vS} S) :
    Module.Injective R R ↔ Module.Injective S S := by
  constructor
  · intro hR
    let : Module.Injective R R := hR
    exact selfInjective_of_equivalence R S e
  · intro hS
    let : Module.Injective S S := hS
    exact selfInjective_of_equivalence S R e.symm

end ModuleCat

end SelfInjectivity
