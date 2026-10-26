/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import SheafCohomology.AcyclicResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.Topology.Sheaves.Abelian

public section

/-!
# Source naturality for injective-resolution Ext comparisons

This file equips the canonical Ext/homology comparison associated to an
injective resolution with contravariant naturality in the Ext source object.
It also records that additive functors preserving injectives and homology send
injective resolutions to injective resolutions.
-/

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe v u

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
  {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D]
  [CategoryWithHomology D]

/-- The injective dual of `mapProjectiveResolution`. -/
@[expose] noncomputable def mapInjectiveResolution (F : C ⥤ D) [F.Additive]
    [F.PreservesInjectiveObjects] [F.PreservesHomology]
    {Z : C} (I : InjectiveResolution Z) :
    InjectiveResolution (F.obj Z) where
  cocomplex := (F.mapHomologicalComplex _).obj I.cocomplex
  injective n := PreservesInjectiveObjects.injective_obj (I.injective n)
  ι :=
    (HomologicalComplex.singleMapHomologicalComplex F
      (ComplexShape.up ℕ) 0).inv.app Z ≫
      (F.mapHomologicalComplex _).map I.ι
  quasiIso := inferInstance

end CategoryTheory.Functor

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]

/-- Every injective resolution is acyclic for `Ext X -`. -/
@[expose] noncomputable def AcyclicResolution.ofInjectiveResolution (X : C) {Z : C}
    (I : InjectiveResolution Z) : AcyclicResolution X Z where
  cocomplex := I.cocomplex
  ι := I.ι
  quasiIso := inferInstance
  extAcyclic n q hq := by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    exact subsingleton_of_injective X (I.cocomplex.X n) q

end CategoryTheory.Abelian.Ext

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]

namespace AcyclicResolution

variable {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X)

/-- Precomposition on Ext, with the source and target functors exposed in a
form convenient for exact cokernel constructions. -/
noncomputable abbrev extSourceMap (n : ℕ) (Y : C) :
    (extFunctorObj X n).obj Y ⟶ (extFunctorObj X' n).obj Y :=
  ((extFunctor n).map g.op).app Y

/-- Precomposition on the degree-zero Ext complexes of a fixed injective
resolution. -/
@[expose] noncomputable def injectiveExtZeroComplexSourceMap :
    (AcyclicResolution.ofInjectiveResolution X I).extZeroComplex ⟶
      (AcyclicResolution.ofInjectiveResolution X' I).extZeroComplex where
  f n := extSourceMap g 0 (I.cocomplex.X n)
  comm' i j _ := by
    change ((extFunctor 0).map g.op).app (I.cocomplex.X i) ≫
        ((extFunctor 0).obj (op X')).map (I.cocomplex.d i j) =
      ((extFunctor 0).obj (op X)).map (I.cocomplex.d i j) ≫
        ((extFunctor 0).map g.op).app (I.cocomplex.X j)
    exact (((extFunctor 0).map g.op).naturality
      (I.cocomplex.d i j)).symm

/-- Precomposition on the additive-coyoneda complexes of a fixed injective
resolution. -/
@[expose] noncomputable def injectiveHomComplexSourceMap :
    (AcyclicResolution.ofInjectiveResolution X I).homComplex ⟶
      (AcyclicResolution.ofInjectiveResolution X' I).homComplex where
  f n := (preadditiveCoyoneda.map g.op).app (I.cocomplex.X n)
  comm' i j _ := ((preadditiveCoyoneda.map g.op).naturality
    (I.cocomplex.d i j)).symm

/-- Precomposition on the cokernels used in the degree-one dimension shift. -/
@[expose] noncomputable def covariantCokernelSourceMap {S : ShortComplex C} :
    cokernel (AddCommGrpCat.ofHom
        ((Ext.mk₀ S.g).postcomp X (add_zero 0))) ⟶
      cokernel (AddCommGrpCat.ofHom
        ((Ext.mk₀ S.g).postcomp X' (add_zero 0))) :=
  cokernel.map _ _
    (AddCommGrpCat.ofHom
      ((Ext.mk₀ g).precomp S.X₂ (zero_add 0)))
    (AddCommGrpCat.ofHom
      ((Ext.mk₀ g).precomp S.X₃ (zero_add 0)))
    (by
      ext x
      dsimp
      symm
      apply Ext.comp_assoc <;> omega)

/-- The covariant connecting equivalence is contravariantly natural in the
source object. -/
lemma covariantDimensionShift_source_naturality {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Ext X S.X₂ n)]
    [Subsingleton (Ext X S.X₂ (n + 1))]
    [Subsingleton (Ext X' S.X₂ n)]
    [Subsingleton (Ext X' S.X₂ (n + 1))]
    (x : Ext X S.X₃ n) :
    covariantDimensionShift hS X' n
        ((Ext.mk₀ g).comp x (zero_add n)) =
      (Ext.mk₀ g).comp (covariantDimensionShift hS X n x)
        (zero_add (n + 1)) := by
  dsimp [covariantDimensionShift]
  apply Ext.comp_assoc <;> omega

private lemma cast_source {Y : C} {p r : ℕ} (h : p = r)
    (x : Ext X Y p) :
    AddEquiv.cast h ((Ext.mk₀ g).comp x (zero_add p)) =
      (Ext.mk₀ g).comp (AddEquiv.cast h x) (zero_add r) := by
  subst r
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The iterated cycle dimension shift for a fixed injective resolution is
contravariantly natural in its source. -/
lemma injectiveCyclesDimensionShiftIterate_source_naturality
    (n q : ℕ) (hq : 0 < q)
    (x : Ext X (I.cocomplex.cycles n) q) :
    (AcyclicResolution.ofInjectiveResolution X' I
      ).cyclesDimensionShiftIterate n q hq
        ((Ext.mk₀ g).comp x (zero_add q)) =
      (Ext.mk₀ g).comp
        ((AcyclicResolution.ofInjectiveResolution X I
          ).cyclesDimensionShiftIterate n q hq x)
        (zero_add (n + q)) := by
  induction n generalizing q with
  | zero =>
      dsimp [cyclesDimensionShiftIterate]
      apply cast_source g
  | succ n ih =>
      dsimp only [cyclesDimensionShiftIterate]
      simp only [AddEquiv.trans_apply]
      have hshift :
          (AcyclicResolution.ofInjectiveResolution X' I
            ).cyclesDimensionShift n q hq
              ((Ext.mk₀ g).comp x (zero_add q)) =
            (Ext.mk₀ g).comp
              ((AcyclicResolution.ofInjectiveResolution X I
                ).cyclesDimensionShift n q hq x)
              (zero_add (q + 1)) := by
        let _ : Subsingleton (Ext X
            ((AcyclicResolution.ofInjectiveResolution X I
              ).cyclesShortComplex n).X₂ q) := by
          change Subsingleton (Ext X (I.cocomplex.X n) q)
          exact (AcyclicResolution.ofInjectiveResolution X I
            ).extAcyclic n q hq
        let _ : Subsingleton (Ext X
            ((AcyclicResolution.ofInjectiveResolution X I
              ).cyclesShortComplex n).X₂ (q + 1)) := by
          change Subsingleton (Ext X (I.cocomplex.X n) (q + 1))
          exact (AcyclicResolution.ofInjectiveResolution X I
            ).extAcyclic n (q + 1) (by omega)
        let _ : Subsingleton (Ext X'
            ((AcyclicResolution.ofInjectiveResolution X I
              ).cyclesShortComplex n).X₂ q) := by
          change Subsingleton (Ext X' (I.cocomplex.X n) q)
          exact (AcyclicResolution.ofInjectiveResolution X' I
            ).extAcyclic n q hq
        let _ : Subsingleton (Ext X'
            ((AcyclicResolution.ofInjectiveResolution X I
              ).cyclesShortComplex n).X₂ (q + 1)) := by
          change Subsingleton (Ext X' (I.cocomplex.X n) (q + 1))
          exact (AcyclicResolution.ofInjectiveResolution X' I
            ).extAcyclic n (q + 1) (by omega)
        change
          covariantDimensionShift
              ((AcyclicResolution.ofInjectiveResolution X I
                ).cyclesShortComplex_shortExact n) X' q
              ((Ext.mk₀ g).comp x (zero_add q)) = _
        exact covariantDimensionShift_source_naturality g
          ((AcyclicResolution.ofInjectiveResolution X I
            ).cyclesShortComplex_shortExact n) q x
      rw [hshift]
      rw [ih (q + 1) (by omega)]
      apply cast_source g

set_option backward.isDefEq.respectTransparency false in
/-- The inverse iterated cycle dimension shift for a fixed injective
resolution is contravariantly natural in its source. -/
lemma injectiveCyclesDimensionShiftIterate_symm_source_naturality
    (n q : ℕ) (hq : 0 < q)
    (x : Ext X (I.cocomplex.cycles 0) (n + q)) :
    ((AcyclicResolution.ofInjectiveResolution X' I
      ).cyclesDimensionShiftIterate n q hq).symm
        ((Ext.mk₀ g).comp x (zero_add (n + q))) =
      (Ext.mk₀ g).comp
        (((AcyclicResolution.ofInjectiveResolution X I
          ).cyclesDimensionShiftIterate n q hq).symm x)
        (zero_add q) := by
  apply ((AcyclicResolution.ofInjectiveResolution X' I
    ).cyclesDimensionShiftIterate n q hq).injective
  rw [AddEquiv.apply_symm_apply,
    injectiveCyclesDimensionShiftIterate_source_naturality I g,
    AddEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The connecting isomorphism from a degree-zero cokernel to degree-one Ext
is contravariantly natural in the source object. -/
lemma covariantCokernelIso_source_naturality_apply {S : ShortComplex C}
    (hS : S.ShortExact)
    [Subsingleton (Ext X S.X₂ 1)] [Subsingleton (Ext X' S.X₂ 1)]
    (z : ↑(cokernel (AddCommGrpCat.ofHom
      ((Ext.mk₀ S.g).postcomp X (add_zero 0))))) :
    (covariantCokernelIso hS X').addCommGroupIsoToAddEquiv
        (covariantCokernelSourceMap g z) =
      (Ext.mk₀ g).comp
        ((covariantCokernelIso hS X).addCommGroupIsoToAddEquiv z)
        (zero_add 1) := by
  obtain ⟨x, rfl⟩ := (AddCommGrpCat.epi_iff_surjective
    (cokernel.π (AddCommGrpCat.ofHom
      ((Ext.mk₀ S.g).postcomp X (add_zero 0))))).mp inferInstance z
  have hcoker :
      cokernel.π (AddCommGrpCat.ofHom
          ((Ext.mk₀ S.g).postcomp X (add_zero 0))) ≫
        covariantCokernelSourceMap g =
      AddCommGrpCat.ofHom
          ((Ext.mk₀ g).precomp S.X₃ (zero_add 0)) ≫
        cokernel.π (AddCommGrpCat.ofHom
          ((Ext.mk₀ S.g).postcomp X' (add_zero 0))) := by
    dsimp only [covariantCokernelSourceMap, cokernel.map]
    apply cokernel.π_desc
  have hmap := CategoryTheory.ConcreteCategory.congr_hom hcoker x
  have hX := CategoryTheory.ConcreteCategory.congr_hom
    (cokernelπ_covariantCokernelIso_hom hS X) x
  have hX' := CategoryTheory.ConcreteCategory.congr_hom
    (cokernelπ_covariantCokernelIso_hom hS X')
      (((Ext.mk₀ g).precomp S.X₃ (zero_add 0)) x)
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at hmap
  rw [AddCommGrpCat.comp_apply] at hX hX'
  calc
    _ = (covariantCokernelIso hS X').addCommGroupIsoToAddEquiv
          ((CategoryTheory.ConcreteCategory.hom
            (cokernel.π (AddCommGrpCat.ofHom
              ((Ext.mk₀ S.g).postcomp X' (add_zero 0)))))
            ((CategoryTheory.ConcreteCategory.hom
              (AddCommGrpCat.ofHom
                ((Ext.mk₀ g).precomp S.X₃ (zero_add 0)))) x)) :=
      congrArg (fun z =>
        (covariantCokernelIso hS X').addCommGroupIsoToAddEquiv z) hmap
    _ = (CategoryTheory.ConcreteCategory.hom
          (AddCommGrpCat.ofHom (hS.extClass.postcomp X' rfl)))
          ((CategoryTheory.ConcreteCategory.hom
            (AddCommGrpCat.ofHom
              ((Ext.mk₀ g).precomp S.X₃ (zero_add 0)))) x) := hX'
    _ = (Ext.mk₀ g).comp
          ((CategoryTheory.ConcreteCategory.hom
            (AddCommGrpCat.ofHom (hS.extClass.postcomp X rfl))) x)
          (zero_add 1) := by
      dsimp
      apply Ext.comp_assoc <;> omega
    _ = _ := congrArg (fun y => (Ext.mk₀ g).comp y (zero_add 1)) hX.symm

/-- The cycle-cokernel comparison for a fixed injective resolution, with its
degree-one acyclicity witness encapsulated. -/
@[expose] noncomputable def injectiveCyclesCokernelIso (I : InjectiveResolution A)
    (X : C) (n : ℕ) :
    cokernel ((extFunctorObj X 0).map
      (I.cocomplex.toCycles n (n + 1))) ≅
        ↧(Ext X (I.cocomplex.cycles n) 1) := by
  let _ : Subsingleton (Ext X
      ((AcyclicResolution.ofInjectiveResolution X I
        ).cyclesShortComplex n).X₂ 1) := by
    change Subsingleton (Ext X (I.cocomplex.X n) 1)
    exact (AcyclicResolution.ofInjectiveResolution X I
      ).extAcyclic n 1 (by omega)
  exact (AcyclicResolution.ofInjectiveResolution X I).cyclesCokernelIso n

/-- Precomposition on the dimension-shift cokernels of a fixed injective
resolution. -/
noncomputable abbrev injectiveCyclesCokernelSourceMap (n : ℕ) :=
  show
    cokernel ((extFunctorObj X 0).map
        (I.cocomplex.toCycles n (n + 1))) ⟶
      cokernel ((extFunctorObj X' 0).map
        (I.cocomplex.toCycles n (n + 1)))
  from covariantCokernelSourceMap g
      (S := (AcyclicResolution.ofInjectiveResolution X I
        ).cyclesShortComplex n)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse cycle-cokernel comparison for a fixed injective resolution is
contravariantly natural in its source. -/
lemma injectiveCyclesCokernelIso_inv_source_naturality_apply
    (n : ℕ) (x : Ext X (I.cocomplex.cycles n) 1) :
    (injectiveCyclesCokernelIso I X' n).addCommGroupIsoToAddEquiv.symm
        ((Ext.mk₀ g).comp x (zero_add 1)) =
      injectiveCyclesCokernelSourceMap I g n
        ((injectiveCyclesCokernelIso I X n
          ).addCommGroupIsoToAddEquiv.symm x) := by
  let _ : Subsingleton (Ext X
      ((AcyclicResolution.ofInjectiveResolution X I
        ).cyclesShortComplex n).X₂ 1) := by
    change Subsingleton (Ext X (I.cocomplex.X n) 1)
    exact (AcyclicResolution.ofInjectiveResolution X I
      ).extAcyclic n 1 (by omega)
  let _ : Subsingleton (Ext X'
      ((AcyclicResolution.ofInjectiveResolution X I
        ).cyclesShortComplex n).X₂ 1) := by
    change Subsingleton (Ext X' (I.cocomplex.X n) 1)
    exact (AcyclicResolution.ofInjectiveResolution X' I
      ).extAcyclic n 1 (by omega)
  let _ : Subsingleton (Ext X'
      ((AcyclicResolution.ofInjectiveResolution X' I
        ).cyclesShortComplex n).X₂ 1) := by
    change Subsingleton (Ext X' (I.cocomplex.X n) 1)
    exact (AcyclicResolution.ofInjectiveResolution X' I
      ).extAcyclic n 1 (by omega)
  apply (injectiveCyclesCokernelIso I X' n
    ).addCommGroupIsoToAddEquiv.injective
  rw [AddEquiv.apply_symm_apply]
  symm
  change
    (covariantCokernelIso
        ((AcyclicResolution.ofInjectiveResolution X I
          ).cyclesShortComplex_shortExact n) X'
      ).addCommGroupIsoToAddEquiv
        (covariantCokernelSourceMap g
          ((injectiveCyclesCokernelIso I X n
            ).addCommGroupIsoToAddEquiv.symm x)) = _
  rw [covariantCokernelIso_source_naturality_apply]
  change
    (Ext.mk₀ g).comp
        ((injectiveCyclesCokernelIso I X n).addCommGroupIsoToAddEquiv
          ((injectiveCyclesCokernelIso I X n
            ).addCommGroupIsoToAddEquiv.symm x))
        (zero_add 1) = _
  rw [AddEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Source naturality of the inverse cycle-cokernel comparison, stated with
the native acyclic-resolution comparison. -/
lemma injectiveCyclesCokernelIso_inv_source_naturality_apply_native
    (n : ℕ) (x : Ext X (I.cocomplex.cycles n) 1)
    [Subsingleton (Ext X
      ((AcyclicResolution.ofInjectiveResolution X I
        ).cyclesShortComplex n).X₂ 1)]
    [Subsingleton (Ext X'
      ((AcyclicResolution.ofInjectiveResolution X I
        ).cyclesShortComplex n).X₂ 1)]
    [Subsingleton (Ext X'
      ((AcyclicResolution.ofInjectiveResolution X' I
        ).cyclesShortComplex n).X₂ 1)] :
    ((AcyclicResolution.ofInjectiveResolution X' I
      ).cyclesCokernelIso n).addCommGroupIsoToAddEquiv.symm
        ((Ext.mk₀ g).comp x (zero_add 1)) =
      injectiveCyclesCokernelSourceMap I g n
        (((AcyclicResolution.ofInjectiveResolution X I
          ).cyclesCokernelIso n).addCommGroupIsoToAddEquiv.symm x) := by
  change
    (injectiveCyclesCokernelIso I X' n).addCommGroupIsoToAddEquiv.symm
        ((Ext.mk₀ g).comp x (zero_add 1)) =
      injectiveCyclesCokernelSourceMap I g n
        ((injectiveCyclesCokernelIso I X n
          ).addCommGroupIsoToAddEquiv.symm x)
  exact injectiveCyclesCokernelIso_inv_source_naturality_apply I g n x

set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero Ext/cycles comparison for a fixed injective resolution is
contravariantly natural in its source. -/
@[reassoc]
lemma injectiveExtZeroCyclesIso_hom_source_naturality (n : ℕ) :
    HomologicalComplex.cyclesMap
          (injectiveExtZeroComplexSourceMap I g) n ≫
        ((AcyclicResolution.ofInjectiveResolution X' I
          ).extZeroCyclesIso n).hom =
      ((AcyclicResolution.ofInjectiveResolution X I
        ).extZeroCyclesIso n).hom ≫
        extSourceMap g 0 (I.cocomplex.cycles n) := by
  rw [← cancel_mono ((extFunctorObj X' 0).map
    ((AcyclicResolution.ofInjectiveResolution X' I
      ).cocomplex.iCycles n))]
  simp only [Category.assoc]
  rw [(AcyclicResolution.ofInjectiveResolution X' I
    ).extZeroCyclesIso_hom_map_iCycles]
  rw [HomologicalComplex.cyclesMap_i]
  change
    (AcyclicResolution.ofInjectiveResolution X I
      ).extZeroComplex.iCycles n ≫
        extSourceMap g 0 (I.cocomplex.X n) =
      (((AcyclicResolution.ofInjectiveResolution X I
        ).extZeroCyclesIso n).hom ≫
          extSourceMap g 0 (I.cocomplex.cycles n)) ≫
        (extFunctorObj X' 0).map (I.cocomplex.iCycles n)
  have hcycles := (AcyclicResolution.ofInjectiveResolution X I
    ).extZeroCyclesIso_hom_map_iCycles n
  change
    ((AcyclicResolution.ofInjectiveResolution X I
      ).extZeroCyclesIso n).hom ≫
        (extFunctorObj X 0).map (I.cocomplex.iCycles n) =
      (AcyclicResolution.ofInjectiveResolution X I
        ).extZeroComplex.iCycles n at hcycles
  have hnat := ((extFunctor 0).map g.op).naturality
    (I.cocomplex.iCycles n)
  change
    (extFunctorObj X 0).map (I.cocomplex.iCycles n) ≫
        extSourceMap g 0 (I.cocomplex.X n) =
      extSourceMap g 0 (I.cocomplex.cycles n) ≫
        (extFunctorObj X' 0).map (I.cocomplex.iCycles n) at hnat
  calc
    _ = (((AcyclicResolution.ofInjectiveResolution X I
          ).extZeroCyclesIso n).hom ≫
            (extFunctorObj X 0).map (I.cocomplex.iCycles n)) ≫
          extSourceMap g 0 (I.cocomplex.X n) :=
      congrArg (fun k => k ≫ extSourceMap g 0 (I.cocomplex.X n))
        hcycles.symm
    _ = ((AcyclicResolution.ofInjectiveResolution X I
          ).extZeroCyclesIso n).hom ≫
        ((extFunctorObj X 0).map (I.cocomplex.iCycles n) ≫
          extSourceMap g 0 (I.cocomplex.X n)) := by
      rw [Category.assoc]
    _ = ((AcyclicResolution.ofInjectiveResolution X I
          ).extZeroCyclesIso n).hom ≫
        (extSourceMap g 0 (I.cocomplex.cycles n) ≫
          (extFunctorObj X' 0).map (I.cocomplex.iCycles n)) :=
      congrArg (fun k =>
        ((AcyclicResolution.ofInjectiveResolution X I
          ).extZeroCyclesIso n).hom ≫ k) hnat
    _ = _ := (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Inverse form of source naturality for the degree-zero Ext/cycles
comparison. -/
@[reassoc]
lemma injectiveExtZeroCyclesIso_inv_source_naturality (n : ℕ) :
    extSourceMap g 0 (I.cocomplex.cycles n) ≫
        ((AcyclicResolution.ofInjectiveResolution X' I
          ).extZeroCyclesIso n).inv =
      ((AcyclicResolution.ofInjectiveResolution X I
        ).extZeroCyclesIso n).inv ≫
        HomologicalComplex.cyclesMap
          (injectiveExtZeroComplexSourceMap I g) n := by
  rw [← cancel_epi ((AcyclicResolution.ofInjectiveResolution X I
    ).extZeroCyclesIso n).hom]
  rw [Iso.hom_inv_id_assoc]
  rw [← injectiveExtZeroCyclesIso_hom_source_naturality_assoc]
  rw [Iso.hom_inv_id, Category.comp_id]

/-- The canonical dimension-shift cokernel/homology comparison for a fixed
injective resolution. -/
@[expose] noncomputable def injectiveExtZeroCokernelIsoHomology
    (I : InjectiveResolution A) (X : C) (n : ℕ) :
    cokernel ((extFunctorObj X 0).map
      (I.cocomplex.toCycles n (n + 1))) ≅
        (AcyclicResolution.ofInjectiveResolution X I
          ).extZeroComplex.homology (n + 1) :=
  (AcyclicResolution.ofInjectiveResolution X I
    ).extZeroCokernelIsoHomology n

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma cokernelπ_injectiveExtZeroCokernelIsoHomology_hom (n : ℕ) :
    cokernel.π ((extFunctorObj X 0).map
        (I.cocomplex.toCycles n (n + 1))) ≫
      (injectiveExtZeroCokernelIsoHomology I X n).hom =
        ((AcyclicResolution.ofInjectiveResolution X I
          ).extZeroCyclesIso (n + 1)).inv ≫
          (AcyclicResolution.ofInjectiveResolution X I
            ).extZeroComplex.homologyπ (n + 1) := by
  exact (AcyclicResolution.ofInjectiveResolution X I
    ).cokernelπ_extZeroCokernelIsoHomology_hom n

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma cokernelπ_injectiveCyclesCokernelSourceMap (n : ℕ) :
    cokernel.π ((extFunctorObj X 0).map
        (I.cocomplex.toCycles n (n + 1))) ≫
      injectiveCyclesCokernelSourceMap I g n =
        extSourceMap g 0 (I.cocomplex.cycles (n + 1)) ≫
          cokernel.π ((extFunctorObj X' 0).map
            (I.cocomplex.toCycles n (n + 1))) := by
  dsimp only [injectiveCyclesCokernelSourceMap,
    covariantCokernelSourceMap, cokernel.map]
  apply cokernel.π_desc

set_option backward.isDefEq.respectTransparency false in
/-- The canonical dimension-shift cokernel/homology comparison for a fixed
injective resolution is contravariantly natural in its source. -/
@[reassoc]
lemma injectiveExtZeroCokernelIsoHomology_hom_source_naturality
    (n : ℕ) :
    injectiveCyclesCokernelSourceMap I g n ≫
        (injectiveExtZeroCokernelIsoHomology I X' n).hom =
      (injectiveExtZeroCokernelIsoHomology I X n).hom ≫
        HomologicalComplex.homologyMap
          (injectiveExtZeroComplexSourceMap I g) (n + 1) := by
  let πX := cokernel.π ((extFunctorObj X 0).map
    (I.cocomplex.toCycles n (n + 1)))
  let πX' := cokernel.π ((extFunctorObj X' 0).map
    (I.cocomplex.toCycles n (n + 1)))
  let cMap := injectiveCyclesCokernelSourceMap I g n
  let eX := injectiveExtZeroCokernelIsoHomology I X n
  let eX' := injectiveExtZeroCokernelIsoHomology I X' n
  let τ := extSourceMap g 0 (I.cocomplex.cycles (n + 1))
  let ψ := injectiveExtZeroComplexSourceMap I g
  let zX := (AcyclicResolution.ofInjectiveResolution X I
    ).extZeroCyclesIso (n + 1)
  let zX' := (AcyclicResolution.ofInjectiveResolution X' I
    ).extZeroCyclesIso (n + 1)
  have hcMap : πX ≫ cMap = τ ≫ πX' :=
    cokernelπ_injectiveCyclesCokernelSourceMap I g n
  have heX : πX ≫ eX.hom = zX.inv ≫
      (AcyclicResolution.ofInjectiveResolution X I
        ).extZeroComplex.homologyπ (n + 1) :=
    cokernelπ_injectiveExtZeroCokernelIsoHomology_hom I n
  have heX' : πX' ≫ eX'.hom = zX'.inv ≫
      (AcyclicResolution.ofInjectiveResolution X' I
        ).extZeroComplex.homologyπ (n + 1) :=
    cokernelπ_injectiveExtZeroCokernelIsoHomology_hom I n
  have hz : τ ≫ zX'.inv = zX.inv ≫
      HomologicalComplex.cyclesMap ψ (n + 1) :=
    injectiveExtZeroCyclesIso_inv_source_naturality I g (n + 1)
  have hπ := HomologicalComplex.homologyπ_naturality ψ (n + 1)
  apply (cancel_epi πX).1
  calc
    _ = (πX ≫ cMap) ≫ eX'.hom := (Category.assoc _ _ _).symm
    _ = (τ ≫ πX') ≫ eX'.hom :=
      congrArg (fun k => k ≫ eX'.hom) hcMap
    _ = τ ≫ (πX' ≫ eX'.hom) := Category.assoc _ _ _
    _ = τ ≫ (zX'.inv ≫
          (AcyclicResolution.ofInjectiveResolution X' I
            ).extZeroComplex.homologyπ (n + 1)) :=
      congrArg (fun k => τ ≫ k) heX'
    _ = (τ ≫ zX'.inv) ≫
          (AcyclicResolution.ofInjectiveResolution X' I
            ).extZeroComplex.homologyπ (n + 1) :=
      (Category.assoc _ _ _).symm
    _ = (zX.inv ≫ HomologicalComplex.cyclesMap ψ (n + 1)) ≫
          (AcyclicResolution.ofInjectiveResolution X' I
            ).extZeroComplex.homologyπ (n + 1) :=
      congrArg (fun k => k ≫
        (AcyclicResolution.ofInjectiveResolution X' I
          ).extZeroComplex.homologyπ (n + 1)) hz
    _ = zX.inv ≫ (HomologicalComplex.cyclesMap ψ (n + 1) ≫
          (AcyclicResolution.ofInjectiveResolution X' I
            ).extZeroComplex.homologyπ (n + 1)) :=
      Category.assoc _ _ _
    _ = zX.inv ≫
          ((AcyclicResolution.ofInjectiveResolution X I
            ).extZeroComplex.homologyπ (n + 1) ≫
            HomologicalComplex.homologyMap ψ (n + 1)) :=
      congrArg (fun k => zX.inv ≫ k) hπ.symm
    _ = (zX.inv ≫
          (AcyclicResolution.ofInjectiveResolution X I
            ).extZeroComplex.homologyπ (n + 1)) ≫
          HomologicalComplex.homologyMap ψ (n + 1) :=
      (Category.assoc _ _ _).symm
    _ = (πX ≫ eX.hom) ≫
          HomologicalComplex.homologyMap ψ (n + 1) :=
      congrArg (fun k => k ≫
        HomologicalComplex.homologyMap ψ (n + 1)) heX.symm
    _ = πX ≫ (eX.hom ≫
          HomologicalComplex.homologyMap ψ (n + 1)) :=
      Category.assoc _ _ _

lemma injectiveExtZeroCokernelIsoHomology_hom_source_naturality_apply
    (n : ℕ)
    (z : ↑(cokernel ((extFunctorObj X 0).map
      (I.cocomplex.toCycles n (n + 1))))) :
    (injectiveExtZeroCokernelIsoHomology I X' n
      ).addCommGroupIsoToAddEquiv
        (injectiveCyclesCokernelSourceMap I g n z) =
      HomologicalComplex.homologyMap
        (injectiveExtZeroComplexSourceMap I g) (n + 1)
        ((injectiveExtZeroCokernelIsoHomology I X n
          ).addCommGroupIsoToAddEquiv z) := by
  have h := congrArg (fun k => k z)
    (injectiveExtZeroCokernelIsoHomology_hom_source_naturality I g n)
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Source naturality of the cokernel/homology comparison, stated with the
native acyclic-resolution comparison. -/
lemma injectiveExtZeroCokernelIsoHomology_hom_source_naturality_apply_native
    (n : ℕ)
    (z : ↑(cokernel ((extFunctorObj X 0).map
      (I.cocomplex.toCycles n (n + 1))))) :
    ((AcyclicResolution.ofInjectiveResolution X' I
      ).extZeroCokernelIsoHomology n).addCommGroupIsoToAddEquiv
        (injectiveCyclesCokernelSourceMap I g n z) =
      HomologicalComplex.homologyMap
        (injectiveExtZeroComplexSourceMap I g) (n + 1)
        (((AcyclicResolution.ofInjectiveResolution X I
          ).extZeroCokernelIsoHomology n).addCommGroupIsoToAddEquiv z) := by
  exact injectiveExtZeroCokernelIsoHomology_hom_source_naturality_apply
    I g n z

set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero Ext/coyoneda comparison is contravariantly natural in its
source object. -/
@[reassoc]
lemma extZeroCoyonedaIso_hom_source_naturality (Y : C) :
    extSourceMap g 0 Y ≫ (extZeroCoyonedaIso X').hom.app Y =
      (extZeroCoyonedaIso X).hom.app Y ≫
        (preadditiveCoyoneda.map g.op).app Y := by
  ext x
  change
    Ext.addEquiv₀ ((Ext.mk₀ g).comp x (zero_add 0)) =
      g ≫ Ext.addEquiv₀ x
  apply (Ext.mk₀_bijective X' Y).injective
  rw [Ext.mk₀_addEquiv₀_apply]
  rw [← Ext.mk₀_comp_mk₀]
  rw [Ext.mk₀_addEquiv₀_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The termwise degree-zero Ext/additive-coyoneda complex comparison for a
fixed injective resolution is contravariantly natural in its source. -/
@[reassoc]
lemma injectiveExtZeroComplexIsoHomComplex_hom_source_naturality :
    injectiveExtZeroComplexSourceMap I g ≫
        (AcyclicResolution.ofInjectiveResolution X' I
          ).extZeroComplexIsoHomComplex.hom =
      (AcyclicResolution.ofInjectiveResolution X I
        ).extZeroComplexIsoHomComplex.hom ≫
        injectiveHomComplexSourceMap I g := by
  ext n x
  have h := extZeroCoyonedaIso_hom_source_naturality g
    (I.cocomplex.X n)
  exact CategoryTheory.ConcreteCategory.congr_hom h x

set_option backward.isDefEq.respectTransparency false in
/-- The induced homology comparison between degree-zero Ext and additive
coyoneda for a fixed injective resolution is contravariantly natural in its
source. -/
@[reassoc]
lemma injectiveExtZeroHomologyIsoHomology_hom_source_naturality (n : ℕ) :
    HomologicalComplex.homologyMap
          (injectiveExtZeroComplexSourceMap I g) n ≫
        ((AcyclicResolution.ofInjectiveResolution X' I
          ).extZeroHomologyIsoHomology n).hom =
      ((AcyclicResolution.ofInjectiveResolution X I
        ).extZeroHomologyIsoHomology n).hom ≫
        HomologicalComplex.homologyMap
          (injectiveHomComplexSourceMap I g) n := by
  dsimp [AcyclicResolution.extZeroHomologyIsoHomology,
    HomologicalComplex.homologyMapIso]
  rw [← HomologicalComplex.homologyMap_comp]
  rw [injectiveExtZeroComplexIsoHomComplex_hom_source_naturality]
  rw [HomologicalComplex.homologyMap_comp]

lemma injectiveExtZeroHomologyIsoHomology_hom_source_naturality_apply
    (n : ℕ)
    (z : ↑((AcyclicResolution.ofInjectiveResolution X I
      ).extZeroComplex.homology n)) :
    ((AcyclicResolution.ofInjectiveResolution X' I
      ).extZeroHomologyIsoHomology n).addCommGroupIsoToAddEquiv
        (HomologicalComplex.homologyMap
          (injectiveExtZeroComplexSourceMap I g) n z) =
      HomologicalComplex.homologyMap
        (injectiveHomComplexSourceMap I g) n
        (((AcyclicResolution.ofInjectiveResolution X I
          ).extZeroHomologyIsoHomology n).addCommGroupIsoToAddEquiv z) := by
  have h := congrArg (fun k => k z)
    (injectiveExtZeroHomologyIsoHomology_hom_source_naturality I g n)
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Transport to degree-zero cycles for a fixed injective resolution is
contravariantly natural in the source object. -/
lemma injectiveExtIsoCyclesZero_source_naturality
    (q : ℕ) (x : Ext X A q) :
    (AcyclicResolution.ofInjectiveResolution X' I
      ).extIsoCyclesZero q ((Ext.mk₀ g).comp x (zero_add q)) =
      (Ext.mk₀ g).comp
        ((AcyclicResolution.ofInjectiveResolution X I
          ).extIsoCyclesZero q x) (zero_add q) := by
  have hobj :
      (AcyclicResolution.ofInjectiveResolution X' I
        ).objectIsoCyclesZero.hom =
      (AcyclicResolution.ofInjectiveResolution X I
        ).objectIsoCyclesZero.hom := rfl
  change
    ((Ext.mk₀ g).comp x (zero_add q)).comp
        (Ext.mk₀ (AcyclicResolution.ofInjectiveResolution X' I
          ).objectIsoCyclesZero.hom) (add_zero q) =
      (Ext.mk₀ g).comp
        (x.comp (Ext.mk₀ (AcyclicResolution.ofInjectiveResolution X I
          ).objectIsoCyclesZero.hom) (add_zero q)) (zero_add q)
  rw [hobj]
  apply Ext.comp_assoc
  all_goals omega

lemma injectiveExtZeroHomology_eqToIso_source_naturality_apply
    {m n : ℕ} (h : m = n)
    (z : ↑((AcyclicResolution.ofInjectiveResolution X I
      ).extZeroComplex.homology m)) :
    (eqToIso (congrArg (fun i =>
      (AcyclicResolution.ofInjectiveResolution X' I
        ).extZeroComplex.homology i) h)).addCommGroupIsoToAddEquiv
        (HomologicalComplex.homologyMap
          (injectiveExtZeroComplexSourceMap I g) m z) =
      HomologicalComplex.homologyMap
        (injectiveExtZeroComplexSourceMap I g) n
        ((eqToIso (congrArg (fun i =>
          (AcyclicResolution.ofInjectiveResolution X I
            ).extZeroComplex.homology i) h)).addCommGroupIsoToAddEquiv z) := by
  subst n
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- For a fixed injective resolution, the positive Ext/homology comparison is
contravariantly natural in the source object. -/
lemma injectiveExtPositiveIsoHomology_source_naturality
    (q : ℕ) (hq : 0 < q) (x : Ext X A q) :
    (AcyclicResolution.ofInjectiveResolution X' I
      ).extPositiveIsoHomology q hq
        ((Ext.mk₀ g).comp x (zero_add q)) =
      HomologicalComplex.homologyMap
        (injectiveHomComplexSourceMap I g) q
        ((AcyclicResolution.ofInjectiveResolution X I
          ).extPositiveIsoHomology q hq x) := by
  let _ : Subsingleton (Ext X
      ((AcyclicResolution.ofInjectiveResolution X I
        ).cyclesShortComplex (q - 1)).X₂ 1) := by
    change Subsingleton (Ext X (I.cocomplex.X (q - 1)) 1)
    exact (AcyclicResolution.ofInjectiveResolution X I
      ).extAcyclic (q - 1) 1 (by omega)
  let _ : Subsingleton (Ext X'
      ((AcyclicResolution.ofInjectiveResolution X I
        ).cyclesShortComplex (q - 1)).X₂ 1) := by
    change Subsingleton (Ext X' (I.cocomplex.X (q - 1)) 1)
    exact (AcyclicResolution.ofInjectiveResolution X' I
      ).extAcyclic (q - 1) 1 (by omega)
  let _ : Subsingleton (Ext X'
      ((AcyclicResolution.ofInjectiveResolution X' I
        ).cyclesShortComplex (q - 1)).X₂ 1) := by
    change Subsingleton (Ext X' (I.cocomplex.X (q - 1)) 1)
    exact (AcyclicResolution.ofInjectiveResolution X' I
      ).extAcyclic (q - 1) 1 (by omega)
  dsimp [AcyclicResolution.extPositiveIsoHomology]
  rw [injectiveExtIsoCyclesZero_source_naturality]
  rw [cast_source]
  rw [injectiveCyclesDimensionShiftIterate_symm_source_naturality]
  rw [injectiveCyclesCokernelIso_inv_source_naturality_apply_native]
  rw [injectiveExtZeroCokernelIsoHomology_hom_source_naturality_apply_native]
  rw [injectiveExtZeroHomology_eqToIso_source_naturality_apply]
  rw [injectiveExtZeroHomologyIsoHomology_hom_source_naturality_apply]
  · rfl
  · omega

end AcyclicResolution

end CategoryTheory.Abelian.Ext
