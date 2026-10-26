/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Modules.PresheafChangeOfRings
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Sheaf extension of scalars

For a map of commutative-ring sheaves on one site, sheafify the sectionwise
tensor presheaf. The resulting adjunction is to restriction along the whole
map of ring sheaves. Sections of the sheafification are not asserted to be
sectionwise tensors.

## References

* Mathlib, `Mathlib/Algebra/Category/ModuleCat/Presheaf/Sheafification.lean` and
  `Mathlib/Algebra/Category/ModuleCat/Sheaf/ChangeOfRings.lean` (Joël Riou):
  sheafification of module presheaves and restriction of scalars along a
  morphism of ring sheaves, used in this extension-of-scalars construction.
* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (21 October 2025
  draft), §2.6.4 and Exercise 2.6.K(a) (p. 92): sectionwise tensor presheaf
  followed by sheafification. This arbitrary-site adjunction enables Exercise
  7.2.D(b,c,e) (p. 205), but is not a separately numbered theorem there;
  sheafified sections are not identified with raw tensors.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped ChangeOfRings

universe u v₁ u₁

namespace RingedSpaces.Modules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  (A B : Sheaf J CommRingCat.{u})

/-- Forget commutativity of a sheaf of rings. -/
abbrev ringSheaf (R : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R

/-- A morphism of the underlying sheaves of rings. -/
def ringSheafMap (theta : A ⟶ B) : ringSheaf A ⟶ ringSheaf B where
  hom := ringMap A.obj B.obj theta.hom

/-- Sheaves of modules over a sheaf of commutative rings. -/
abbrev Sheaves (R : Sheaf J CommRingCat.{u}) := SheafOfModules.{u} (ringSheaf R)

variable [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Native sheafification of module presheaves over the existing ring sheaf. -/
noncomputable def moduleSheafification : Presheaves B.obj ⥤ Sheaves B := by
  change PresheafOfModules.{u} (ringSheaf B).obj ⥤ Sheaves B
  letI : Presheaf.IsLocallyInjective J (𝟙 (ringSheaf B).obj) := inferInstance
  letI : Presheaf.IsLocallySurjective J (𝟙 (ringSheaf B).obj) := inferInstance
  exact PresheafOfModules.sheafification (𝟙 (ringSheaf B).obj)

/-- The native adjunction governing module sheafification. -/
noncomputable def moduleSheafificationAdjunction :
    moduleSheafification B ⊣
      SheafOfModules.forget (ringSheaf B) ⋙
        PresheafOfModules.restrictScalars (𝟙 (ringSheaf B).obj) := by
  change PresheafOfModules.sheafification (𝟙 (ringSheaf B).obj) ⊣ _
  exact PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf B).obj)

/-- The tensor sheaf; arbitrary-open sections need not be pure tensors. -/
noncomputable def tensorSheaf (theta : A ⟶ B) (M : Sheaves A) : Sheaves B :=
  (moduleSheafification B).obj (tensorPresheaf A.obj B.obj theta.hom M.val)

/-- The explicit sheaf extension-of-scalars functor. -/
noncomputable def tensorSheafFunctor (theta : A ⟶ B) : Sheaves A ⥤ Sheaves B :=
  (SheafOfModules.forget (ringSheaf A)) ⋙
    tensorPresheafFunctor A.obj B.obj theta.hom ⋙ moduleSheafification B

/-- The natural Hom equivalence for the sheafified tensor presheaf. -/
noncomputable def tensorSheafHomEquiv (theta : A ⟶ B) (M : Sheaves A) (N : Sheaves B) :
    ((tensorSheafFunctor A B theta).obj M ⟶ N) ≃
      (M ⟶ (SheafOfModules.restrictScalars (ringSheafMap A B theta)).obj N) :=
  ((moduleSheafificationAdjunction B).homEquiv
      (tensorPresheaf A.obj B.obj theta.hom M.val) N).trans
    ((tensorPresheafHomEquiv A.obj B.obj theta.hom M.val N.val).trans
      ((SheafOfModules.fullyFaithfulForget (ringSheaf A)).homEquiv
        (X := M) (Y := (SheafOfModules.restrictScalars (ringSheafMap A B theta)).obj N)).symm)

/-- After forgetting the sheaf structure, the Hom equivalence restricts a map to `1 ⊗ m`. -/
theorem tensorSheafHomEquiv_val (theta : A ⟶ B) (M : Sheaves A) (N : Sheaves B)
    (t : (tensorSheafFunctor A B theta).obj M ⟶ N) :
    (SheafOfModules.forget (ringSheaf A)).map (tensorSheafHomEquiv A B theta M N t) =
      tensorPresheafHomDown A.obj B.obj theta.hom M.val
        ((moduleSheafificationAdjunction B).homEquiv
          (tensorPresheaf A.obj B.obj theta.hom M.val) N t) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The sheaf Hom map evaluates via the actual sheafification unit and `1 ⊗ m`. -/
theorem tensorSheafHomEquiv_apply (theta : A ⟶ B) (M : Sheaves A) (N : Sheaves B)
    (t : (tensorSheafFunctor A B theta).obj M ⟶ N) (U : Cᵒᵖ) (m : M.val.obj U) :
    (tensorSheafHomEquiv A B theta M N t).val.app U m =
      t.val.app U
        ((PresheafOfModules.Hom.app
          ((moduleSheafificationAdjunction B).unit.app
            (tensorPresheaf A.obj B.obj theta.hom M.val)) U)
          (tensorUnitSection A.obj B.obj theta.hom M.val U m)) := by
  have h := tensorSheafHomEquiv_val A B theta M N t
  have hEval := congrArg (fun g : M.val ⟶
      (PresheafOfModules.restrictScalars (ringMap A.obj B.obj theta.hom)).obj N.val =>
      g.app U m) h
  change (tensorSheafHomEquiv A B theta M N t).val.app U m =
    (tensorSectionHomEquiv A.obj B.obj theta.hom M.val U (N.val.obj U))
      (((moduleSheafificationAdjunction B).homEquiv _ N t).app U) m at hEval
  rw [tensorSectionHomEquiv_apply] at hEval
  have hAdj := (moduleSheafificationAdjunction B).homEquiv_unit
    (tensorPresheaf A.obj B.obj theta.hom M.val) N t
  have hApp := congrArg (fun g : tensorPresheaf A.obj B.obj theta.hom M.val ⟶ N.val =>
      g.app U (tensorUnitSection A.obj B.obj theta.hom M.val U m)) hAdj
  exact hEval.trans hApp

theorem tensorSheafHomEquiv_naturality_left (theta : A ⟶ B)
    {M M' : Sheaves A} (h : M ⟶ M') (N : Sheaves B)
    (t : (tensorSheafFunctor A B theta).obj M' ⟶ N) :
    tensorSheafHomEquiv A B theta M N ((tensorSheafFunctor A B theta).map h ≫ t) =
      h ≫ tensorSheafHomEquiv A B theta M' N t := by
  apply (SheafOfModules.forget (ringSheaf A)).map_injective
  rw [tensorSheafHomEquiv_val, Functor.map_comp, tensorSheafHomEquiv_val]
  change tensorPresheafHomDown A.obj B.obj theta.hom M.val
      ((moduleSheafificationAdjunction B).homEquiv _ N
        ((moduleSheafification B).map
          ((tensorPresheafFunctor A.obj B.obj theta.hom).map h.val) ≫ t)) =
    h.val ≫ tensorPresheafHomDown A.obj B.obj theta.hom M'.val
      ((moduleSheafificationAdjunction B).homEquiv _ N t)
  have hAdj := (moduleSheafificationAdjunction B).homEquiv_naturality_left
    ((tensorPresheafFunctor A.obj B.obj theta.hom).map h.val) t
  exact (congrArg (tensorPresheafHomDown A.obj B.obj theta.hom M.val) hAdj).trans
    (tensorPresheafHomDown_naturality_left A.obj B.obj theta.hom h.val _)

theorem tensorSheafHomEquiv_naturality_right (theta : A ⟶ B)
    (M : Sheaves A) {N N' : Sheaves B}
    (t : (tensorSheafFunctor A B theta).obj M ⟶ N) (k : N ⟶ N') :
    tensorSheafHomEquiv A B theta M N' (t ≫ k) =
      tensorSheafHomEquiv A B theta M N t ≫
        (SheafOfModules.restrictScalars (ringSheafMap A B theta)).map k := by
  apply (SheafOfModules.forget (ringSheaf A)).map_injective
  rw [tensorSheafHomEquiv_val, Functor.map_comp, tensorSheafHomEquiv_val]
  change tensorPresheafHomDown A.obj B.obj theta.hom M.val
      ((moduleSheafificationAdjunction B).homEquiv _ N' (t ≫ k)) =
    tensorPresheafHomDown A.obj B.obj theta.hom M.val
        ((moduleSheafificationAdjunction B).homEquiv _ N t) ≫
      (PresheafOfModules.restrictScalars (ringMap A.obj B.obj theta.hom)).map k.val
  have hAdj := (moduleSheafificationAdjunction B).homEquiv_naturality_right t k
  exact (congrArg (tensorPresheafHomDown A.obj B.obj theta.hom M.val) hAdj).trans
    (tensorPresheafHomDown_naturality_right A.obj B.obj theta.hom M.val _ k.val)

/-- Extension by sheafified tensor is left adjoint to restriction of scalars. -/
noncomputable def tensorSheafAdjunction (theta : A ⟶ B) :
    tensorSheafFunctor A B theta ⊣
      SheafOfModules.restrictScalars (ringSheafMap A B theta) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := tensorSheafHomEquiv A B theta
    homEquiv_naturality_left_symm := by
      intro M M' N h g
      apply (tensorSheafHomEquiv A B theta M N).injective
      rw [Equiv.apply_symm_apply]
      rw [tensorSheafHomEquiv_naturality_left A B theta h N
        ((tensorSheafHomEquiv A B theta M' N).symm g)]
      rw [Equiv.apply_symm_apply]
    homEquiv_naturality_right := by
      intro M N N' t k
      exact tensorSheafHomEquiv_naturality_right A B theta M t k }

set_option backward.isDefEq.respectTransparency false in
/-- The sheaf unit on `m` is the sheafification of `1 ⊗ m`. -/
theorem tensorSheafAdjunction_unit (theta : A ⟶ B) (M : Sheaves A)
    (U : Cᵒᵖ) (m : M.val.obj U) :
    ((tensorSheafAdjunction A B theta).unit.app M).val.app U m =
      (PresheafOfModules.Hom.app
        ((moduleSheafificationAdjunction B).unit.app
          (tensorPresheaf A.obj B.obj theta.hom M.val)) U)
        (tensorUnitSection A.obj B.obj theta.hom M.val U m) := by
  change (tensorSectionHomEquiv A.obj B.obj theta.hom M.val U _)
      (PresheafOfModules.Hom.app
        ((moduleSheafificationAdjunction B).unit.app
          (tensorPresheaf A.obj B.obj theta.hom M.val)) U) m = _
  exact tensorSectionHomEquiv_apply A.obj B.obj theta.hom M.val U _ _ m

private noncomputable def sheafCounitPresheafMap (theta : A ⟶ B) (N : Sheaves B) :
    tensorPresheaf A.obj B.obj theta.hom
        ((SheafOfModules.restrictScalars (ringSheafMap A B theta)).obj N).val ⟶ N.val :=
  (moduleSheafificationAdjunction B).homEquiv _ N
    ((tensorSheafAdjunction A B theta).counit.app N)

set_option backward.isDefEq.respectTransparency false in
private theorem sheafCounitPresheafMap_eq (theta : A ⟶ B) (N : Sheaves B) :
    sheafCounitPresheafMap A B theta N =
      (tensorPresheafAdjunction A.obj B.obj theta.hom).counit.app N.val := by
  let M := (SheafOfModules.restrictScalars (ringSheafMap A B theta)).obj N
  have hCounit : tensorSheafHomEquiv A B theta M N
      ((tensorSheafAdjunction A B theta).counit.app N) = 𝟙 M := by
    change (tensorSheafHomEquiv A B theta M N)
      ((tensorSheafHomEquiv A B theta M N).symm (𝟙 M)) = 𝟙 M
    exact (tensorSheafHomEquiv A B theta M N).apply_symm_apply (𝟙 M)
  have hForget := congrArg (SheafOfModules.forget (ringSheaf A)).map hCounit
  rw [tensorSheafHomEquiv_val] at hForget
  change tensorPresheafHomDown A.obj B.obj theta.hom M.val
    (sheafCounitPresheafMap A B theta N) = 𝟙 M.val at hForget
  apply (tensorPresheafHomEquiv A.obj B.obj theta.hom M.val N.val).injective
  change tensorPresheafHomDown A.obj B.obj theta.hom M.val
    (sheafCounitPresheafMap A B theta N) =
      tensorPresheafHomDown A.obj B.obj theta.hom M.val
        ((tensorPresheafAdjunction A.obj B.obj theta.hom).counit.app N.val)
  rw [hForget]
  change (𝟙 M.val) = (tensorPresheafHomEquiv A.obj B.obj theta.hom M.val N.val)
    ((tensorPresheafHomEquiv A.obj B.obj theta.hom M.val N.val).symm (𝟙 M.val))
  exact ((tensorPresheafHomEquiv A.obj B.obj theta.hom M.val N.val).apply_symm_apply
    (𝟙 M.val)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The sheaf counit extends `b ⊗ n ↦ b • n` through the genuine sheafification unit. -/
theorem tensorSheafAdjunction_counit (theta : A ⟶ B) (N : Sheaves B)
    (U : Cᵒᵖ) (b : B.obj.obj U) (n : N.val.obj U) :
    ((tensorSheafAdjunction A B theta).counit.app N).val.app U
        ((PresheafOfModules.Hom.app
          ((moduleSheafificationAdjunction B).unit.app
            (tensorPresheaf A.obj B.obj theta.hom
              ((SheafOfModules.restrictScalars (ringSheafMap A B theta)).obj N).val)) U)
          (b • tensorUnitSection A.obj B.obj theta.hom
            ((SheafOfModules.restrictScalars (ringSheafMap A B theta)).obj N).val U n)) =
      b • n := by
  let M := (SheafOfModules.restrictScalars (ringSheafMap A B theta)).obj N
  let P := tensorPresheaf A.obj B.obj theta.hom M.val
  let element := b • tensorUnitSection A.obj B.obj theta.hom M.val U n
  have hAdj : sheafCounitPresheafMap A B theta N =
      (moduleSheafificationAdjunction B).unit.app P ≫
        ((SheafOfModules.forget (ringSheaf B)) ⋙
          PresheafOfModules.restrictScalars (𝟙 (ringSheaf B).obj)).map
            ((tensorSheafAdjunction A B theta).counit.app N) :=
    (moduleSheafificationAdjunction B).homEquiv_unit P N
      ((tensorSheafAdjunction A B theta).counit.app N)
  calc
    _ = (sheafCounitPresheafMap A B theta N).app U element := by
      have hEval := congrArg (fun h : P ⟶ N.val => h.app U element) hAdj
      exact hEval.symm
    _ = b • n := by
      rw [sheafCounitPresheafMap_eq]
      exact tensorPresheafAdjunction_counit A.obj B.obj theta.hom N.val U b n

/-- The topological open site supplies native weak sheafification. -/
theorem opensWeakSheafify (X : TopCat.{u}) :
    HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := by
  infer_instance

/-- The topological open site satisfies native local-bijection detection. -/
theorem opensWEqualsLocallyBijective (X : TopCat.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  infer_instance

/-- A topological open site discharges every sheaf-level hypothesis at matched universes. -/
noncomputable def opensTensorSheafAdjunction {X : TopCat.{u}}
    (A B : TopCat.Sheaf CommRingCat.{u} X) (theta : A ⟶ B) :
    tensorSheafFunctor A B theta ⊣
      SheafOfModules.restrictScalars (ringSheafMap A B theta) := by
  let : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    opensWeakSheafify X
  let : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    opensWEqualsLocallyBijective X
  exact tensorSheafAdjunction A B theta

end RingedSpaces.Modules
