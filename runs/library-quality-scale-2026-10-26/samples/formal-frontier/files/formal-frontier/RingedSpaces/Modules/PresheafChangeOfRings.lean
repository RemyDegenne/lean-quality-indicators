/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# Presheaf extension of scalars

Given a full natural transformation of commutative-ring presheaves, construct the
sectionwise tensor presheaf and its extension/restriction adjunction. Restriction
is obtained as a mate of the semilinear restriction on pure tensors, and does
not require a topology or a sheaf condition.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (21 October 2025
  draft), §2.6.4 and Exercise 2.6.K(a) (p. 92): tensor presheaves followed by
  sheafification motivate scalar extension. This arbitrary-site presheaf
  adjunction is an enabling project construction for Exercise 7.2.D(b,c,e)
  (p. 205), not a separately numbered fixed-site theorem there.
-/

@[expose] public section

open CategoryTheory
open scoped ChangeOfRings

universe u v₁ u₁

namespace RingedSpaces.Modules

variable {C : Type u₁} [Category.{v₁} C] (A B : Cᵒᵖ ⥤ CommRingCat.{u})

/-- The underlying presheaf of possibly noncommutative rings. -/
abbrev ringPresheaf (R : Cᵒᵖ ⥤ CommRingCat.{u}) : Cᵒᵖ ⥤ RingCat.{u} :=
  R ⋙ forget₂ CommRingCat RingCat.{u}

/-- Forget commutativity of a whole map of ring presheaves. -/
def ringMap (theta : A ⟶ B) : ringPresheaf A ⟶ ringPresheaf B :=
  Functor.whiskerRight theta (forget₂ CommRingCat RingCat.{u})

/-- Module presheaves over a presheaf of commutative rings. -/
abbrev Presheaves (R : Cᵒᵖ ⥤ CommRingCat.{u}) :=
  PresheafOfModulesOfCommRing.{u} R

/-- The actual tensor of sections, with its `B(U)` action. -/
noncomputable def tensorSection (theta : A ⟶ B) (M : Presheaves A)
    (U : Cᵒᵖ) : ModuleCat.{u} ((ringPresheaf B).obj U) :=
  letI : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  letI : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  (ModuleCat.extendScalars ((ringMap A B theta).app U).hom).obj (M.obj U)

/-- The sectionwise unit `m ↦ 1 ⊗ m`. -/
noncomputable def tensorUnitSection (theta : A ⟶ B) (M : Presheaves A)
    (U : Cᵒᵖ) : M.obj U ⟶
      (ModuleCat.restrictScalars ((ringMap A B theta).app U).hom).obj
        (tensorSection A B theta M U) := by
  letI : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  letI : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  exact (ModuleCat.extendRestrictScalarsAdj ((ringMap A B theta).app U).hom).unit.app
    (M.obj U)

/-- The ordinary tensor Hom equivalence on a single open. -/
noncomputable def tensorSectionHomEquiv (theta : A ⟶ B) (M : Presheaves A)
    (U : Cᵒᵖ) (N : ModuleCat.{u} ((ringPresheaf B).obj U)) :
    (tensorSection A B theta M U ⟶ N) ≃
      (M.obj U ⟶ (ModuleCat.restrictScalars ((ringMap A B theta).app U).hom).obj N) := by
  letI : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  letI : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  exact (ModuleCat.extendRestrictScalarsAdj ((ringMap A B theta).app U).hom).homEquiv _ _

theorem tensorSectionHomEquiv_apply (theta : A ⟶ B) (M : Presheaves A)
    (U : Cᵒᵖ) (N : ModuleCat.{u} ((ringPresheaf B).obj U))
    (t : tensorSection A B theta M U ⟶ N) (m : M.obj U) :
    tensorSectionHomEquiv A B theta M U N t m = t (tensorUnitSection A B theta M U m) := by
  let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  exact ModuleCat.extendRestrictScalarsAdj_homEquiv_apply t m

theorem tensorSectionHomEquiv_symm_unit (theta : A ⟶ B) (M : Presheaves A)
    (U : Cᵒᵖ) (N : ModuleCat.{u} ((ringPresheaf B).obj U))
    (g : M.obj U ⟶
      (ModuleCat.restrictScalars ((ringMap A B theta).app U).hom).obj N)
    (m : M.obj U) :
    (tensorSectionHomEquiv A B theta M U N).symm g
        (tensorUnitSection A B theta M U m) = g m := by
  let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  rw [← tensorSectionHomEquiv_apply A B theta M U N]
  exact congrArg (fun h => h m)
    ((tensorSectionHomEquiv A B theta M U N).apply_symm_apply g)

/-- The restriction mate of `m ↦ 1 ⊗ m|`, linear over `A(U)`. -/
noncomputable def restrictionUnit (theta : A ⟶ B) (M : Presheaves A)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    M.obj U ⟶
      (ModuleCat.restrictScalars ((ringMap A B theta).app U).hom).obj
        ((ModuleCat.restrictScalars ((ringPresheaf B).map f).hom).obj
          (tensorSection A B theta M V)) := by
  letI : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  letI : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  letI : CommRing ((ringPresheaf A).obj V) := inferInstanceAs (CommRing (A.obj V))
  letI : CommRing ((ringPresheaf B).obj V) := inferInstanceAs (CommRing (B.obj V))
  letI : Module (A.obj U) (M.obj U) := (M.obj U).isModule
  letI : Module (A.obj V) (M.obj V) := (M.obj V).isModule
  letI : Module (B.obj V)
      ((ModuleCat.restrictScalars ((ringMap A B theta).app V).hom).obj
        (tensorSection A B theta M V)) :=
    (tensorSection A B theta M V).isModule
  letI : Module ((ringPresheaf A).obj U)
      ((ModuleCat.restrictScalars ((ringPresheaf B).map f).hom).obj
        (tensorSection A B theta M V)) :=
    ((ModuleCat.restrictScalars ((ringMap A B theta).app U).hom).obj
      ((ModuleCat.restrictScalars ((ringPresheaf B).map f).hom).obj
        (tensorSection A B theta M V))).isModule
  let h : M.obj U ⟶
      (ModuleCat.restrictScalars ((ringMap A B theta).app U).hom).obj
        ((ModuleCat.restrictScalars ((ringPresheaf B).map f).hom).obj
          (tensorSection A B theta M V)) :=
    ModuleCat.ofHom {
      toFun := fun m => tensorUnitSection A B theta M V (M.map f m)
      map_add' := by
        intro m n
        change tensorUnitSection A B theta M V (M.map f (m + n)) = _
        rw [map_add]
        exact (tensorUnitSection A B theta M V).hom.map_add _ _
      map_smul' := by
        intro a m
        have htheta : (theta.app V).hom ((A.map f).hom a) =
            (B.map f).hom ((theta.app U).hom a) := by
          have naturality := theta.naturality f
          exact congrArg (fun h : A.obj U ⟶ B.obj V => h a) naturality
        change tensorUnitSection A B theta M V (M.map f (a • m)) =
          (B.map f).hom ((theta.app U).hom a) •
            tensorUnitSection A B theta M V (M.map f m)
        rw [M.map_smul, ← htheta]
        exact (tensorUnitSection A B theta M V).hom.map_smul _ _ }
  exact h

/-- The `B(U)`-linear restriction mate, targeting the restriction along `B(U) → B(V)`. -/
noncomputable def tensorRestriction (theta : A ⟶ B) (M : Presheaves A)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    tensorSection A B theta M U ⟶
      (ModuleCat.restrictScalars ((ringPresheaf B).map f).hom).obj
        (tensorSection A B theta M V) :=
  (tensorSectionHomEquiv A B theta M U _).symm (restrictionUnit A B theta M f)

theorem restrictionUnit_apply (theta : A ⟶ B) (M : Presheaves A)
    {U V : Cᵒᵖ} (f : U ⟶ V) (m : M.obj U) :
    restrictionUnit A B theta M f m = tensorUnitSection A B theta M V (M.map f m) := rfl

theorem tensorRestriction_unit (theta : A ⟶ B) (M : Presheaves A)
    {U V : Cᵒᵖ} (f : U ⟶ V) (m : M.obj U) :
    tensorRestriction A B theta M f (tensorUnitSection A B theta M U m) =
      tensorUnitSection A B theta M V (M.map f m) := by
  let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  have h := (tensorSectionHomEquiv A B theta M U _).apply_symm_apply
    (restrictionUnit A B theta M f)
  have hm := congrArg (fun k => k m) h
  rw [← restrictionUnit_apply A B theta M f m]
  change (tensorSectionHomEquiv A B theta M U _)
      (tensorRestriction A B theta M f) m = restrictionUnit A B theta M f m
  exact hm

set_option backward.isDefEq.respectTransparency false in
/-- Restriction sends an arbitrary `b ⊗ m` to `B(f)(b) ⊗ M(f)(m)`. -/
theorem tensorRestriction_smul (theta : A ⟶ B) (M : Presheaves A)
    {U V : Cᵒᵖ} (f : U ⟶ V) (b : B.obj U) (m : M.obj U) :
    tensorRestriction A B theta M f (b • tensorUnitSection A B theta M U m) =
      B.map f b • tensorUnitSection A B theta M V (M.map f m) := by
  let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  let : CommRing ((ringPresheaf B).obj V) := inferInstanceAs (CommRing (B.obj V))
  rw [map_smul, tensorRestriction_unit]
  rfl

/-- The genuine pointwise tensor presheaf, including its identity and composition laws. -/
noncomputable def tensorPresheaf (theta : A ⟶ B) (M : Presheaves A) :
    Presheaves B :=
  PresheafOfModulesOfCommRing.mk (fun U => tensorSection A B theta M U)
    (fun f => tensorRestriction A B theta M f)
    (map_id := by
      intro U
      let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
      let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
      apply ModuleCat.ExtendScalars.hom_ext
      intro m
      change tensorRestriction A B theta M (𝟙 U)
        (tensorUnitSection A B theta M U m) = tensorUnitSection A B theta M U m
      rw [tensorRestriction_unit]
      simp
      rfl)
    (map_comp := by
      intro U V W f g
      let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
      let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
      apply ModuleCat.ExtendScalars.hom_ext
      intro m
      change tensorRestriction A B theta M (f ≫ g) (tensorUnitSection A B theta M U m) =
        tensorRestriction A B theta M g
          (tensorRestriction A B theta M f (tensorUnitSection A B theta M U m))
      rw [tensorRestriction_unit A B theta M (f ≫ g) m]
      rw [tensorRestriction_unit A B theta M f m]
      rw [tensorRestriction_unit A B theta M g (M.map f m)]
      rw [M.map_comp_apply f g m])

/-- The section map `b ⊗ m ↦ b ⊗ h(m)` induced by an `A`-linear sheaf map. -/
noncomputable def tensorSectionMap (theta : A ⟶ B) {M N : Presheaves A} (h : M ⟶ N)
    (U : Cᵒᵖ) : tensorSection A B theta M U ⟶ tensorSection A B theta N U := by
  letI : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  letI : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  exact (ModuleCat.extendScalars ((ringMap A B theta).app U).hom).map (h.app U)

theorem tensorSectionMap_unit (theta : A ⟶ B) {M N : Presheaves A} (h : M ⟶ N)
    (U : Cᵒᵖ) (m : M.obj U) :
    tensorSectionMap A B theta h U (tensorUnitSection A B theta M U m) =
      tensorUnitSection A B theta N U (h.app U m) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Maps of tensor presheaves act on arbitrary pure tensors. -/
theorem tensorSectionMap_smul (theta : A ⟶ B) {M N : Presheaves A} (h : M ⟶ N)
    (U : Cᵒᵖ) (b : B.obj U) (m : M.obj U) :
    tensorSectionMap A B theta h U (b • tensorUnitSection A B theta M U m) =
      b • tensorUnitSection A B theta N U (h.app U m) := by
  let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  rw [map_smul, tensorSectionMap_unit]

/-- Tensoring a map is compatible with all presheaf restrictions. -/
noncomputable def tensorPresheafMap (theta : A ⟶ B) {M N : Presheaves A} (h : M ⟶ N) :
    tensorPresheaf A B theta M ⟶ tensorPresheaf A B theta N :=
  PresheafOfModulesOfCommRing.homMk (fun U => tensorSectionMap A B theta h U)
    (fun {U V} f => by
      let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
      let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
      apply ModuleCat.ExtendScalars.hom_ext
      intro m
      change tensorSectionMap A B theta h V
        (tensorRestriction A B theta M f (tensorUnitSection A B theta M U m)) =
        tensorRestriction A B theta N f
          (tensorSectionMap A B theta h U (tensorUnitSection A B theta M U m))
      rw [tensorRestriction_unit A B theta M f m]
      rw [tensorSectionMap_unit A B theta h V (M.map f m)]
      rw [tensorSectionMap_unit A B theta h U m]
      rw [tensorRestriction_unit A B theta N f (h.app U m)]
      congr 1
      exact PresheafOfModules.naturality_apply h f m)

/-- The covariant tensor presheaf functor. -/
noncomputable def tensorPresheafFunctor (theta : A ⟶ B) :
    Presheaves A ⥤ Presheaves B where
  obj M := tensorPresheaf A B theta M
  map h := tensorPresheafMap A B theta h
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
    let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change tensorSectionMap A B theta (𝟙 M) U (tensorUnitSection A B theta M U m) =
      tensorUnitSection A B theta M U m
    rw [tensorSectionMap_unit]
    rfl
  map_comp h k := by
    apply PresheafOfModules.hom_ext
    intro U
    let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
    let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change tensorSectionMap A B theta (h ≫ k) U (tensorUnitSection A B theta _ U m) =
      tensorSectionMap A B theta k U
        (tensorSectionMap A B theta h U (tensorUnitSection A B theta _ U m))
    rw [tensorSectionMap_unit, tensorSectionMap_unit, tensorSectionMap_unit]
    rfl

/-- The natural presheaf unit before sheafification. -/
noncomputable def presheafTensorUnit (theta : A ⟶ B) (M : Presheaves A) :
    M ⟶ (PresheafOfModules.restrictScalars (ringMap A B theta)).obj
      (tensorPresheaf A B theta M) :=
  { app := fun U => tensorUnitSection A B theta M U
    naturality := fun {U V} f => by
      ext m
      change tensorUnitSection A B theta M V (M.map f m) =
        tensorRestriction A B theta M f (tensorUnitSection A B theta M U m)
      exact (tensorRestriction_unit A B theta M f m).symm }

/-- Restrict a presheaf Hom along the local unit `m ↦ 1 ⊗ m`. -/
noncomputable def tensorPresheafHomDown (theta : A ⟶ B) (M : Presheaves A)
    {N : Presheaves B}
    (t : tensorPresheaf A B theta M ⟶ N) :
    M ⟶ (PresheafOfModules.restrictScalars (ringMap A B theta)).obj N :=
  { app := fun U => tensorSectionHomEquiv A B theta M U (N.obj U) (t.app U)
    naturality := fun {U V} f => by
      ext m
      change tensorSectionHomEquiv A B theta M V (N.obj V) (t.app V) (M.map f m) =
        N.map f (tensorSectionHomEquiv A B theta M U (N.obj U) (t.app U) m)
      rw [tensorSectionHomEquiv_apply A B theta M V (N.obj V) (t.app V)
        (M.map f m)]
      rw [tensorSectionHomEquiv_apply A B theta M U (N.obj U) (t.app U) m]
      rw [← tensorRestriction_unit A B theta M f m]
      exact PresheafOfModules.naturality_apply t f (tensorUnitSection A B theta M U m) }

/-- Extend an `A`-linear presheaf Hom by `b ⊗ m ↦ b • g(m)`. -/
noncomputable def tensorPresheafHomUp (theta : A ⟶ B) (M : Presheaves A)
    {N : Presheaves B}
    (g : M ⟶ (PresheafOfModules.restrictScalars (ringMap A B theta)).obj N) :
    tensorPresheaf A B theta M ⟶ N :=
  { app := fun U => (tensorSectionHomEquiv A B theta M U (N.obj U)).symm (g.app U)
    naturality := fun {U V} f => by
      let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
      let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
      apply ModuleCat.ExtendScalars.hom_ext
      intro m
      change (tensorSectionHomEquiv A B theta M V (N.obj V)).symm (g.app V)
        (tensorRestriction A B theta M f (tensorUnitSection A B theta M U m)) =
          N.map f ((tensorSectionHomEquiv A B theta M U (N.obj U)).symm (g.app U)
            (tensorUnitSection A B theta M U m))
      rw [tensorRestriction_unit A B theta M f m]
      rw [tensorSectionHomEquiv_symm_unit A B theta M V (N.obj V) (g.app V)
        (M.map f m)]
      rw [tensorSectionHomEquiv_symm_unit A B theta M U (N.obj U) (g.app U) m]
      exact PresheafOfModules.naturality_apply g f m }

set_option backward.isDefEq.respectTransparency false in
/-- The upward Hom map evaluates `b ⊗ m` as `b • g(m)` for arbitrary `b`. -/
theorem tensorPresheafHomUp_smul (theta : A ⟶ B) (M : Presheaves A)
    {N : Presheaves B}
    (g : M ⟶ (PresheafOfModules.restrictScalars (ringMap A B theta)).obj N)
    (U : Cᵒᵖ) (b : B.obj U) (m : M.obj U) :
    letI : Module (B.obj U)
      (((PresheafOfModules.restrictScalars (ringMap A B theta)).obj N).obj U) :=
      (N.obj U).isModule
    (tensorPresheafHomUp A B theta M g).app U
        (b • tensorUnitSection A B theta M U m) = b • g.app U m := by
  let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  change (tensorSectionHomEquiv A B theta M U (N.obj U)).symm (g.app U)
    (b • tensorUnitSection A B theta M U m) = _
  rw [map_smul, tensorSectionHomEquiv_symm_unit]
  rfl

/-- The inverse tensor Hom maps, proven compatible with restrictions. -/
noncomputable def tensorPresheafHomEquiv (theta : A ⟶ B) (M : Presheaves A)
    (N : Presheaves B) :
    (tensorPresheaf A B theta M ⟶ N) ≃
      (M ⟶ (PresheafOfModules.restrictScalars (ringMap A B theta)).obj N) where
  toFun := tensorPresheafHomDown A B theta M
  invFun := tensorPresheafHomUp A B theta M
  left_inv t := by
    apply PresheafOfModules.hom_ext
    intro U
    change (tensorSectionHomEquiv A B theta M U (N.obj U)).symm
      ((tensorSectionHomEquiv A B theta M U (N.obj U)) (t.app U)) = t.app U
    exact (tensorSectionHomEquiv A B theta M U (N.obj U)).symm_apply_apply _
  right_inv g := by
    apply PresheafOfModules.hom_ext
    intro U
    change (tensorSectionHomEquiv A B theta M U (N.obj U))
      ((tensorSectionHomEquiv A B theta M U (N.obj U)).symm (g.app U)) = g.app U
    exact (tensorSectionHomEquiv A B theta M U (N.obj U)).apply_symm_apply _

theorem tensorPresheafHomDown_naturality_left (theta : A ⟶ B) {M M' : Presheaves A}
    (h : M ⟶ M') {N : Presheaves B}
    (t : tensorPresheaf A B theta M' ⟶ N) :
    tensorPresheafHomDown A B theta M
        ((tensorPresheafFunctor A B theta).map h ≫ t) =
      h ≫ tensorPresheafHomDown A B theta M' t := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change tensorSectionHomEquiv A B theta M U (N.obj U)
      (tensorSectionMap A B theta h U ≫ t.app U) m =
        tensorSectionHomEquiv A B theta M' U (N.obj U) (t.app U) (h.app U m)
  rw [tensorSectionHomEquiv_apply A B theta M U (N.obj U)
    (tensorSectionMap A B theta h U ≫ t.app U) m]
  rw [tensorSectionHomEquiv_apply A B theta M' U (N.obj U) (t.app U)
    (h.app U m)]
  change t.app U (tensorSectionMap A B theta h U (tensorUnitSection A B theta M U m)) = _
  rw [tensorSectionMap_unit A B theta h U m]
  rfl

theorem tensorPresheafHomDown_naturality_right (theta : A ⟶ B) (M : Presheaves A)
    {N N' : Presheaves B}
    (t : tensorPresheaf A B theta M ⟶ N) (k : N ⟶ N') :
    tensorPresheafHomDown A B theta M (t ≫ k) =
      tensorPresheafHomDown A B theta M t ≫
        (PresheafOfModules.restrictScalars (ringMap A B theta)).map k := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change tensorSectionHomEquiv A B theta M U (N'.obj U) (t.app U ≫ k.app U) m =
    k.app U (tensorSectionHomEquiv A B theta M U (N.obj U) (t.app U) m)
  rw [tensorSectionHomEquiv_apply A B theta M U (N'.obj U) (t.app U ≫ k.app U) m]
  rw [tensorSectionHomEquiv_apply A B theta M U (N.obj U) (t.app U) m]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Sectionwise scalar extension is left adjoint to restriction along the full ring map. -/
noncomputable def tensorPresheafAdjunction (theta : A ⟶ B) :
    tensorPresheafFunctor A B theta ⊣ PresheafOfModules.restrictScalars (ringMap A B theta) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := tensorPresheafHomEquiv A B theta
    homEquiv_naturality_left_symm := by
      intro M M' N h g
      dsimp only [tensorPresheafFunctor]
      apply (tensorPresheafHomEquiv A B theta M N).injective
      rw [Equiv.apply_symm_apply]
      symm
      change tensorPresheafHomDown A B theta M
          ((tensorPresheafFunctor A B theta).map h ≫
            (tensorPresheafHomEquiv A B theta M' N).symm g) = h ≫ g
      rw [tensorPresheafHomDown_naturality_left]
      change h ≫ (tensorPresheafHomEquiv A B theta M' N)
        ((tensorPresheafHomEquiv A B theta M' N).symm g) = h ≫ g
      rw [Equiv.apply_symm_apply]
    homEquiv_naturality_right := by
      intro M N N' t k
      exact tensorPresheafHomDown_naturality_right A B theta M t k }

/-- The adjunction unit is the actual sectionwise map `m ↦ 1 ⊗ m`. -/
theorem tensorPresheafAdjunction_unit (theta : A ⟶ B) (M : Presheaves A)
    (U : Cᵒᵖ) (m : M.obj U) :
    ((tensorPresheafAdjunction A B theta).unit.app M).app U m =
      tensorUnitSection A B theta M U m := by
  change (tensorSectionHomEquiv A B theta M U _)
    (𝟙 (tensorSection A B theta M U)) m = _
  rw [tensorSectionHomEquiv_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
/-- The adjunction counit sends `b ⊗ n` to `b • n` on every section. -/
theorem tensorPresheafAdjunction_counit (theta : A ⟶ B) (N : Presheaves B)
    (U : Cᵒᵖ) (b : B.obj U)
    (n : N.obj U) :
    ((tensorPresheafAdjunction A B theta).counit.app N).app U
        (b • tensorUnitSection A B theta
          ((PresheafOfModules.restrictScalars (ringMap A B theta)).obj N) U n) =
      b • n := by
  let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  change (tensorSectionHomEquiv A B theta _ U (N.obj U)).symm
      (PresheafOfModules.Hom.app
        (𝟙 ((PresheafOfModules.restrictScalars (ringMap A B theta)).obj N)) U)
    (b • tensorUnitSection A B theta _ U n) = _
  rw [map_smul, tensorSectionHomEquiv_symm_unit]
  rfl

end RingedSpaces.Modules
