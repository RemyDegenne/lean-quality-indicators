/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import SheafCohomology.FlasqueAcyclicSections

public section

/-!
# Filtered colimits and sheaf cohomology

This file constructs an acyclic resolution of a filtered colimit by taking
the degreewise filtered colimit of the functorial flasque resolutions.  The
construction retains the canonical map from every stage and does not assert
that the flasque-resolution functor itself preserves filtered colimits.

The present API has the same small-universe boundary as the functorial flasque
resolution and its acyclic-resolution packaging.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace TopCat

namespace HomologicalComplex

universe uI vI uC vC uD vD uι

variable {I : Type uI} [Category.{vI} I]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
variable [HasColimitsOfShape I C] [HasColimitsOfShape I D]
variable {ι : Type uι} {c : ComplexShape ι}
variable (G : C ⥤ D) [G.Additive]

/-- The canonical comparison from the degreewise colimit after mapping a
complex of diagrams to mapping its degreewise colimit. -/
@[expose] noncomputable def colimMapComparison (K : HomologicalComplex (I ⥤ C) c) :
    ((colim (J := I) (C := D)).mapHomologicalComplex c).obj
        (((Functor.whiskeringRight I C D).obj G).mapHomologicalComplex c |>.obj K) ⟶
      (G.mapHomologicalComplex c).obj
        (((colim (J := I) (C := C)).mapHomologicalComplex c).obj K) where
  f n := colimit.post (K.X n) G
  comm' n m _ := colimit.map_post (K.d n m) G

noncomputable instance colimMapComparison_isIso
    (K : HomologicalComplex (I ⥤ C) c)
    [∀ n, PreservesColimit (K.X n) G] : IsIso (colimMapComparison G K) := by
  suffices ∀ n, IsIso ((colimMapComparison G K).f n) by
    apply Hom.isIso_of_components
  intro n
  change IsIso (colimit.post (K.X n) G)
  infer_instance

/-- The canonical comparison is an isomorphism when the mapped functor
preserves the colimit of every term. -/
@[expose] noncomputable def colimMapIso (K : HomologicalComplex (I ⥤ C) c)
    [∀ n, PreservesColimit (K.X n) G] :
    ((colim (J := I) (C := D)).mapHomologicalComplex c).obj
        (((Functor.whiskeringRight I C D).obj G).mapHomologicalComplex c |>.obj K) ≅
      (G.mapHomologicalComplex c).obj
        (((colim (J := I) (C := C)).mapHomologicalComplex c).obj K) :=
  asIso (colimMapComparison G K)

section HomologyColimit

universe uT vT uA vA uκ

variable {T : Type uT} [Category.{vT} T]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {κ : Type uκ} {shape : ComplexShape κ}

/-- Package a functor to complexes as a complex in the functor category. -/
@[reducible, expose]
def ofFunctor (D : T ⥤ HomologicalComplex A shape) :
    HomologicalComplex (T ⥤ A) shape where
  X n := D ⋙ eval A shape n
  d n m :=
    { app := fun t => (D.obj t).d n m
      naturality := fun t t' f => (D.map f).comm n m }
  shape n m h := by
    ext t
    exact (D.obj t).shape n m h
  d_comp_d' n m k hnm hmk := by
    ext t
    exact (D.obj t).d_comp_d n m k

/-- Evaluation of the packaged complex recovers the original complex. -/
@[expose] def ofFunctorAsFunctorIso (D : T ⥤ HomologicalComplex A shape) :
    (ofFunctor D).asFunctor ≅ D :=
  NatIso.ofComponents
    (fun _ => Hom.isoOfComponents (fun _ => Iso.refl _) (by
      intro n m h
      change 𝟙 _ ≫ (D.obj _).d n m = (D.obj _).d n m ≫ 𝟙 _
      simp))
    (by
      intro t t' f
      ext n
      change (D.map f).f n ≫ 𝟙 _ = 𝟙 _ ≫ (D.map f).f n
      simp)

set_option backward.isDefEq.respectTransparency false in
/-- Homology after evaluating a complex of functors is naturally the
evaluation of its functor-category homology object. -/
@[expose] noncomputable def asFunctorHomologyIso
    (K : HomologicalComplex (T ⥤ A) shape) (n : κ) :
    K.asFunctor ⋙ homologyFunctor A shape n ≅ K.homology n :=
  NatIso.ofComponents
    (fun t => (K.sc n).mapHomologyIso ((evaluation T A).obj t))
    (fun {t t'} f => by
      change
        ShortComplex.homologyMap
            ((K.sc n).mapNatTrans ((evaluation T A).map f)) ≫
              ((K.sc n).mapHomologyIso ((evaluation T A).obj t')).hom =
          ((K.sc n).mapHomologyIso ((evaluation T A).obj t)).hom ≫
            ((evaluation T A).map f).app (K.sc n).homology
      rw [ShortComplex.homologyMap_mapNatTrans]
      simp)

/-- Pointwise homology of a diagram of complexes is naturally the homology
object of the corresponding complex in the functor category. -/
@[expose] noncomputable def pointwiseHomologyIso
    (D : T ⥤ HomologicalComplex A shape) (n : κ) :
    D ⋙ homologyFunctor A shape n ≅ (ofFunctor D).homology n :=
  (Functor.isoWhiskerRight (ofFunctorAsFunctorIso D).symm
      (homologyFunctor A shape n)) ≪≫
    asFunctorHomologyIso (ofFunctor D) n

variable [HasColimitsOfShape T A]

/-- The canonical natural transformation from evaluation at one diagram
stage to the colimit functor. -/
@[expose] noncomputable def evaluationToColim (t : T) :
    (evaluation T A).obj t ⟶ colim (J := T) (C := A) where
  app D := colimit.ι D t
  naturality _ _ f := (ι_colimMap f t).symm

/-- The canonical map from one complex in a diagram to the degreewise
colimit of the packaged diagram. -/
@[expose] noncomputable def ofFunctorColimitι
    (D : T ⥤ HomologicalComplex A shape) (t : T) :
    D.obj t ⟶
      ((colim (J := T) (C := A)).mapHomologicalComplex shape).obj
        (ofFunctor D) where
  f n := colimit.ι (D ⋙ eval A shape n) t
  comm' n m _ := ι_colimMap ((ofFunctor D).d n m) t

set_option backward.isDefEq.respectTransparency false in
/-- The degreewise colimit of the packaged complex is canonically the colimit
of the original diagram of complexes. -/
@[expose] noncomputable def ofFunctorColimIso
    (D : T ⥤ HomologicalComplex A shape) :
    ((colim (J := T) (C := A)).mapHomologicalComplex shape).obj (ofFunctor D) ≅
      colimit D :=
  Hom.isoOfComponents
    (fun n =>
      (colimit.isColimit (D ⋙ eval A shape n)).coconePointUniqueUpToIso
        (isColimitOfPreserves (eval A shape n) (colimit.isColimit D)))
    (by
      intro n m h
      apply colimit.hom_ext
      intro t
      have hn : colimit.ι (D ⋙ eval A shape n) t ≫
          ((colimit.isColimit (D ⋙ eval A shape n)).coconePointUniqueUpToIso
            (isColimitOfPreserves (eval A shape n) (colimit.isColimit D))).hom =
            (colimit.ι D t).f n := by
        exact IsColimit.comp_coconePointUniqueUpToIso_hom
          (colimit.isColimit (D ⋙ eval A shape n))
          (isColimitOfPreserves (eval A shape n) (colimit.isColimit D)) t
      have hm : colimit.ι (D ⋙ eval A shape m) t ≫
          ((colimit.isColimit (D ⋙ eval A shape m)).coconePointUniqueUpToIso
            (isColimitOfPreserves (eval A shape m) (colimit.isColimit D))).hom =
            (colimit.ι D t).f m := by
        exact IsColimit.comp_coconePointUniqueUpToIso_hom
          (colimit.isColimit (D ⋙ eval A shape m))
          (isColimitOfPreserves (eval A shape m) (colimit.isColimit D)) t
      simp only [← Category.assoc]
      change
        (colimit.ι (D ⋙ eval A shape n) t ≫ _) ≫ (colimit D).d n m =
          (colimit.ι (D ⋙ eval A shape n) t ≫
            colimMap ((ofFunctor D).d n m)) ≫ _
      rw [hn, ι_colimMap, Category.assoc, hm]
      exact (colimit.ι D t).comm n m)

@[reassoc]
theorem ofFunctorColimitι_comp_ofFunctorColimIso_hom
    (D : T ⥤ HomologicalComplex A shape) (t : T) :
    ofFunctorColimitι D t ≫ (ofFunctorColimIso D).hom = colimit.ι D t := by
  ext n
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (D ⋙ eval A shape n))
    (isColimitOfPreserves (eval A shape n) (colimit.isColimit D)) t

/-- Homology commutes with a colimit when the colimit functor preserves the
relevant homology short complex. -/
@[expose] noncomputable def homologyColimitIso
    (D : T ⥤ HomologicalComplex A shape) (n : κ)
    [(colim (J := T) (C := A)).PreservesLeftHomologyOf ((ofFunctor D).sc n)] :
    colimit (D ⋙ homologyFunctor A shape n) ≅ (colimit D).homology n :=
  (colim (J := T) (C := A)).mapIso (pointwiseHomologyIso D n) ≪≫
    (((ofFunctor D).sc n).mapHomologyIso
      (colim (J := T) (C := A))).symm ≪≫
    homologyMapIso (ofFunctorColimIso D) n

omit [HasColimitsOfShape T A] in
set_option backward.isDefEq.respectTransparency false in
lemma pointwiseHomologyIso_hom_app
    (D : T ⥤ HomologicalComplex A shape) (n : κ) (t : T) :
    (pointwiseHomologyIso D n).hom.app t =
      (((ofFunctor D).sc n).mapHomologyIso
        ((evaluation T A).obj t)).hom := by
  change
    homologyMap ((ofFunctorAsFunctorIso D).inv.app t) n ≫
        (((ofFunctor D).sc n).mapHomologyIso
          ((evaluation T A).obj t)).hom = _
  have h : (ofFunctorAsFunctorIso D).inv.app t = 𝟙 _ := by
    ext i
    rfl
  rw [h, homologyMap_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem homologyColimitIso_hom_ι
    (D : T ⥤ HomologicalComplex A shape) (n : κ)
    [(colim (J := T) (C := A)).PreservesLeftHomologyOf ((ofFunctor D).sc n)]
    [(colim (J := T) (C := A)).PreservesRightHomologyOf ((ofFunctor D).sc n)]
    (t : T) :
    colimit.ι (D ⋙ homologyFunctor A shape n) t ≫
        (homologyColimitIso D n).hom =
      homologyMap (colimit.ι D t) n := by
  dsimp only [homologyColimitIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc]
  change
    (colimit.ι (D ⋙ homologyFunctor A shape n) t ≫
      colimMap (pointwiseHomologyIso D n).hom) ≫ _ = _
  rw [ι_colimMap]
  rw [pointwiseHomologyIso_hom_app]
  change
    ((((ofFunctor D).sc n).mapHomologyIso
          ((evaluation T A).obj t)).hom ≫
        colimit.ι ((ofFunctor D).sc n).homology t) ≫
      ((((ofFunctor D).sc n).mapHomologyIso
          (colim (J := T) (C := A))).inv ≫
        homologyMap (ofFunctorColimIso D).hom n) = _
  have hs := congrArg
    (fun f => f ≫ homologyMap (ofFunctorColimIso D).hom n)
    (ShortComplex.homologyMap_mapNatTrans ((ofFunctor D).sc n)
      (evaluationToColim t)).symm
  calc
    _ = ShortComplex.homologyMap
          (((ofFunctor D).sc n).mapNatTrans (evaluationToColim t)) ≫
        homologyMap (ofFunctorColimIso D).hom n := by
      simpa only [Category.assoc, evaluationToColim, Iso.symm_hom] using hs
    _ = homologyMap (colimit.ι D t) n := by
      change
        homologyMap (ofFunctorColimitι D t) n ≫
            homologyMap (ofFunctorColimIso D).hom n = _
      rw [← homologyMap_comp]
      rw [ofFunctorColimitι_comp_ofFunctorColimIso_hom]

end HomologyColimit

end HomologicalComplex

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

section AcyclicResolutionSections

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
variable [hExt : HasExt.{0} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{0})]
variable {A B : CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{0}}

/-- Additive coyoneda from the constant integral sheaf is naturally terminal-
open sections. -/
@[expose] noncomputable def coyonedaIsoSections :
    preadditiveCoyoneda.obj (op
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
          ↧(ULift ℤ))) ≅
      SheafCohomology.CompactOpenSections.sections
        (X := X) (⊤ : Opens X) :=
  (Abelian.Ext.extZeroCoyonedaIso
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
      ↧(ULift ℤ))).symm ≪≫
    SheafCohomology.DegreeZero.functorHZeroIsoSections (X := X)

/-- The additive equivalence computing positive-degree Ext from an acyclic
resolution, packaged as an isomorphism with the exact bundled source object. -/
@[expose] noncomputable def _root_.CategoryTheory.Abelian.Ext.AcyclicResolution.extPositiveIsoHomologyIso
    (R : Abelian.Ext.AcyclicResolution
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        ↧(ULift ℤ)) A)
    (q : ℕ) (hq : 0 < q) :
    (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) q).obj A ≅ R.homComplex.homology q where
  hom := AddCommGrpCat.ofHom (R.extPositiveIsoHomology q hq).toAddMonoidHom
  inv := AddCommGrpCat.ofHom (R.extPositiveIsoHomology q hq).symm.toAddMonoidHom
  hom_inv_id := by ext x; exact (R.extPositiveIsoHomology q hq).symm_apply_apply x
  inv_hom_id := by ext x; exact (R.extPositiveIsoHomology q hq).apply_symm_apply x

/-- Positive-degree cohomology computed by an acyclic resolution is the
homology of that resolution after taking terminal-open sections. -/
@[expose] noncomputable def _root_.CategoryTheory.Abelian.Ext.AcyclicResolution.positiveIsoSectionsHomology
    (R : Abelian.Ext.AcyclicResolution
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        ↧(ULift ℤ)) A)
    (q : ℕ) (hq : 0 < q) :
    (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) q).obj A ≅
      (((SheafCohomology.CompactOpenSections.sections
        (X := X) (⊤ : Opens X)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj R.cocomplex).homology q :=
  R.extPositiveIsoHomologyIso q hq ≪≫
    HomologicalComplex.homologyMapIso
      ((NatIso.mapHomologicalComplex (coyonedaIsoSections (X := X))
        (ComplexShape.up ℕ)).app R.cocomplex) q

/-- Morphism form of naturality for the positive-degree acyclic-resolution
comparison. -/
@[reassoc]
lemma _root_.CategoryTheory.Abelian.Ext.AcyclicResolution.extPositiveIsoHomology_hom_naturality
    (R : Abelian.Ext.AcyclicResolution
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        ↧(ULift ℤ)) A)
    (R' : Abelian.Ext.AcyclicResolution
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        ↧(ULift ℤ)) B)
    {f : A ⟶ B} (φ : Abelian.Ext.AcyclicResolution.Hom R R' f)
    (q : ℕ) (hq : 0 < q) :
    (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) q).map f ≫
        (R'.extPositiveIsoHomologyIso q hq).hom =
      (R.extPositiveIsoHomologyIso q hq).hom ≫
        HomologicalComplex.homologyMap (R.homComplexMap R' φ.hom) q := by
  ext x
  exact R.extPositiveIsoHomology_naturality R' φ q hq x

/-- Naturality on homology of the termwise additive-coyoneda/terminal-sections
comparison. -/
@[reassoc]
lemma _root_.CategoryTheory.Abelian.Ext.AcyclicResolution.coyonedaIsoSectionsHomology_hom_naturality
    (R : Abelian.Ext.AcyclicResolution
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        ↧(ULift ℤ)) A)
    (R' : Abelian.Ext.AcyclicResolution
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        ↧(ULift ℤ)) B)
    (f : R.cocomplex ⟶ R'.cocomplex) (q : ℕ) :
    HomologicalComplex.homologyMap (R.homComplexMap R' f) q ≫
        (HomologicalComplex.homologyMapIso
          ((NatIso.mapHomologicalComplex (coyonedaIsoSections (X := X))
            (ComplexShape.up ℕ)).app R'.cocomplex) q).hom =
      (HomologicalComplex.homologyMapIso
        ((NatIso.mapHomologicalComplex (coyonedaIsoSections (X := X))
          (ComplexShape.up ℕ)).app R.cocomplex) q).hom ≫
        HomologicalComplex.homologyMap
          (((SheafCohomology.CompactOpenSections.sections
            (X := X) (⊤ : Opens X)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map f) q := by
  change
    HomologicalComplex.homologyMap (R.homComplexMap R' f) q ≫
        HomologicalComplex.homologyMap
          ((NatIso.mapHomologicalComplex (coyonedaIsoSections (X := X))
            (ComplexShape.up ℕ)).hom.app R'.cocomplex) q =
      HomologicalComplex.homologyMap
          ((NatIso.mapHomologicalComplex (coyonedaIsoSections (X := X))
            (ComplexShape.up ℕ)).hom.app R.cocomplex) q ≫
        HomologicalComplex.homologyMap
          (((SheafCohomology.CompactOpenSections.sections
            (X := X) (⊤ : Opens X)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map f) q
  rw [← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun g => HomologicalComplex.homologyMap g q)
    ((NatIso.mapHomologicalComplex (coyonedaIsoSections (X := X))
      (ComplexShape.up ℕ)).hom.naturality f)

set_option backward.isDefEq.respectTransparency false in
/-- The terminal-sections homology comparison is natural in maps of acyclic
resolutions. -/
@[reassoc]
lemma _root_.CategoryTheory.Abelian.Ext.AcyclicResolution.positiveIsoSectionsHomology_hom_naturality
    (R : Abelian.Ext.AcyclicResolution
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        ↧(ULift ℤ)) A)
    (R' : Abelian.Ext.AcyclicResolution
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        ↧(ULift ℤ)) B)
    {f : A ⟶ B} (φ : Abelian.Ext.AcyclicResolution.Hom R R' f)
    (q : ℕ) (hq : 0 < q) :
    (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) q).map f ≫
        (R'.positiveIsoSectionsHomology q hq).hom =
      (R.positiveIsoSectionsHomology q hq).hom ≫
        HomologicalComplex.homologyMap
          (((SheafCohomology.CompactOpenSections.sections
            (X := X) (⊤ : Opens X)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map φ.hom) q := by
  dsimp only [CategoryTheory.Abelian.Ext.AcyclicResolution.positiveIsoSectionsHomology,
    Iso.trans_hom]
  rw [← Category.assoc,
    R.extPositiveIsoHomology_hom_naturality R' φ q hq]
  simp only [Category.assoc]
  rw [R.coyonedaIsoSectionsHomology_hom_naturality R' φ.hom q]

end AcyclicResolutionSections

variable {I : Type} [SmallCategory I] [IsFiltered I]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
variable (F : I ⥤ Sheaf AddCommGrpCat.{0} X)

/-- The functorial flasque resolutions of a diagram of sheaves, viewed as a
complex in the category of diagrams. -/
noncomputable abbrev filteredFlasqueResolutionComplexDiagram :
    CochainComplex (I ⥤ Sheaf AddCommGrpCat X) ℕ :=
  ((((Functor.whiskeringLeft I (Sheaf AddCommGrpCat X)
    (Sheaf AddCommGrpCat X)).obj F).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (flasqueResolutionNat (X := X)))

/-- The pointwise flasque-resolution augmentations, assembled in the category
of diagrams. -/
@[expose] noncomputable def filteredFlasqueResolutionDiagramAugmentation :
    (CochainComplex.single₀ (I ⥤ Sheaf AddCommGrpCat X)).obj F ⟶
      filteredFlasqueResolutionComplexDiagram F :=
  (CochainComplex.fromSingle₀Equiv
    (filteredFlasqueResolutionComplexDiagram F) F).symm
      ⟨Functor.whiskerLeft F (toFlasqueEnvelope (X := X)), by
        ext i
        change
          (toFlasqueEnvelope (X := X)).app (F.obj i) ≫
              ((toFlasqueEnvelopeQuotient (X := X)).app (F.obj i) ≫
                (toFlasqueEnvelope (X := X)).app
                  ((flasqueEnvelopeQuotientFunctor (X := X)).obj
                    (F.obj i))) = 0
        rw [← Category.assoc]
        have h := congr_app
          (toFlasqueEnvelope_comp_toFlasqueEnvelopeQuotient (X := X))
          (F.obj i)
        change
          (toFlasqueEnvelope (X := X)).app (F.obj i) ≫
            (toFlasqueEnvelopeQuotient (X := X)).app (F.obj i) = 0 at h
        rw [h, zero_comp]⟩

omit [IsFiltered I] in
@[simp]
theorem filteredFlasqueResolutionDiagramAugmentation_f_zero :
    (filteredFlasqueResolutionDiagramAugmentation F).f 0 =
      Functor.whiskerLeft F (toFlasqueEnvelope (X := X)) := by
  exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- Evaluation of the complex of diagrams at a stage agrees with that stage's
functorial flasque resolution. -/
@[expose] noncomputable def filteredFlasqueResolutionComplexDiagramEvalIso (i : I) :
    (((evaluation I (Sheaf AddCommGrpCat X)).obj i).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        (filteredFlasqueResolutionComplexDiagram F) ≅
      flasqueResolution (F.obj i) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)

omit [IsFiltered I] in
@[simp]
theorem filteredFlasqueResolutionComplexDiagramEvalIso_inv_f
    (i : I) (n : ℕ) :
    (filteredFlasqueResolutionComplexDiagramEvalIso F i).inv.f n = 𝟙 _ := by
  rfl

omit [IsFiltered I] in
theorem filteredFlasqueResolutionDiagramAugmentation_evaluation (i : I) :
    (((evaluation I (Sheaf AddCommGrpCat X)).obj i).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
        (filteredFlasqueResolutionDiagramAugmentation F) =
      (HomologicalComplex.singleMapHomologicalComplex
        ((evaluation I (Sheaf AddCommGrpCat X)).obj i)
        (ComplexShape.up ℕ) 0).hom.app F ≫
          toFlasqueResolution (F.obj i) ≫
            (filteredFlasqueResolutionComplexDiagramEvalIso F i).inv := by
  ext n
  cases n with
  | zero =>
      change (toFlasqueEnvelope (X := X)).app (F.obj i) = _
      simp [filteredFlasqueResolutionComplexDiagramEvalIso,
        toFlasqueResolution_f_zero]
      change _ = _ ≫ 𝟙 _
      simp
  | succ n => rfl

noncomputable instance filteredFlasqueResolutionDiagramAugmentation_quasiIso :
    QuasiIso (filteredFlasqueResolutionDiagramAugmentation F) := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro i
  rw [filteredFlasqueResolutionDiagramAugmentation_evaluation F i]
  infer_instance

/-- The degreewise filtered colimit of the functorial flasque resolutions. -/
noncomputable abbrev filteredFlasqueResolution :
    CochainComplex (Sheaf AddCommGrpCat X) ℕ :=
  ((colim (J := I) (C := Sheaf AddCommGrpCat X)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (filteredFlasqueResolutionComplexDiagram F)

/-- The augmentation from the colimit sheaf to the degreewise colimit of the
stagewise flasque resolutions. -/
@[expose] noncomputable def filteredFlasqueResolutionAugmentation :
    (CochainComplex.single₀ (Sheaf AddCommGrpCat X)).obj (colimit F) ⟶
      filteredFlasqueResolution F :=
  (HomologicalComplex.singleMapHomologicalComplex
      (colim (J := I) (C := Sheaf AddCommGrpCat X))
      (ComplexShape.up ℕ) 0).inv.app F ≫
    ((colim (J := I) (C := Sheaf AddCommGrpCat X)).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
        (filteredFlasqueResolutionDiagramAugmentation F)

noncomputable instance filteredFlasqueResolutionAugmentation_quasiIso :
    QuasiIso (filteredFlasqueResolutionAugmentation F) := by
  dsimp only [filteredFlasqueResolutionAugmentation]
  infer_instance

/-- Every term of the filtered-colimit resolution is quasi-flasque. -/
theorem filteredFlasqueResolution_isQuasiFlasque
    [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]
    (n : ℕ) : IsQuasiFlasque ((filteredFlasqueResolution F).X n) := by
  let _ : ∀ i, IsQuasiFlasque
      (((filteredFlasqueResolutionComplexDiagram F).X n).obj i) := fun i => by
    change IsQuasiFlasque ((flasqueResolution (F.obj i)).X n)
    infer_instance
  exact IsQuasiFlasque.isQuasiFlasque_colimit
    (filteredFlasqueResolutionComplexDiagram F |>.X n)

variable [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]
variable [hExt : HasExt.{0} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{0})]

/-- The degreewise filtered-colimit resolution, packaged as a resolution
acyclic for the Ext functor defining sheaf cohomology. -/
@[expose] noncomputable def filteredFlasqueAcyclicResolution :
    Abelian.Ext.AcyclicResolution
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        ↧(ULift ℤ))
      ((colim (J := I) (C := Sheaf AddCommGrpCat.{0} X)).obj F) where
  cocomplex := filteredFlasqueResolution F
  ι := filteredFlasqueResolutionAugmentation F
  quasiIso := filteredFlasqueResolutionAugmentation_quasiIso F
  extAcyclic n q hq := by
    let _ : IsQuasiFlasque ((filteredFlasqueResolution F).X n) :=
      filteredFlasqueResolution_isQuasiFlasque F n
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    exact IsQuasiFlasque.subsingleton_H_succ q
      ((filteredFlasqueResolution F).X n)

/-- The canonical map from one stage's complex to the degreewise filtered
colimit complex. -/
@[expose] noncomputable def filteredFlasqueResolutionComplexColimitι (i : I) :
    (((evaluation I (Sheaf AddCommGrpCat X)).obj i).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (filteredFlasqueResolutionComplexDiagram F) ⟶
      filteredFlasqueResolution F where
  f n := colimit.ι (filteredFlasqueResolutionComplexDiagram F |>.X n) i
  comm' n m _ := ι_colimMap
    (filteredFlasqueResolutionComplexDiagram F |>.d n m) i

/-- The canonical map from a stage's flasque resolution to the degreewise
filtered colimit resolution. -/
@[expose] noncomputable def filteredFlasqueResolutionι (i : I) :
    flasqueResolution (F.obj i) ⟶ filteredFlasqueResolution F :=
  (filteredFlasqueResolutionComplexDiagramEvalIso F i).inv ≫
    filteredFlasqueResolutionComplexColimitι F i

omit [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]
  [HasExt (CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{0})] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem filteredFlasqueResolution_stage (i : I) :
    (CochainComplex.single₀ (Sheaf AddCommGrpCat X)).map (colimit.ι F i) ≫
        filteredFlasqueResolutionAugmentation F =
      toFlasqueResolution (F.obj i) ≫ filteredFlasqueResolutionι F i := by
  ext
  simp [filteredFlasqueResolutionAugmentation,
    filteredFlasqueResolutionι,
    filteredFlasqueResolutionComplexColimitι,
    toFlasqueResolution_f_zero]

/-- The canonical stage map, packaged as a map from the stagewise acyclic
resolution to the filtered-colimit acyclic resolution. -/
@[expose] noncomputable def filteredFlasqueAcyclicResolutionHom (i : I) :
    Abelian.Ext.AcyclicResolution.Hom
      (flasqueAcyclicResolution (F.obj i))
      (filteredFlasqueAcyclicResolution F) (colimit.ι F i) where
  hom := filteredFlasqueResolutionι F i
  ι_f_zero_comp_hom_f_zero := by
    have h := congrArg (fun f => f.f 0)
      (filteredFlasqueResolution_stage F i).symm
    exact h

/-- The terminal-sections complexes of the stagewise functorial flasque
resolutions. -/
noncomputable abbrev filteredFlasqueResolutionSectionsDiagram :
    I ⥤ CochainComplex AddCommGrpCat ℕ :=
  F ⋙ (flasqueResolutionNat (X := X)).asFunctor ⋙
    (SheafCohomology.CompactOpenSections.sections
      (X := X) (⊤ : Opens X)).mapHomologicalComplex (ComplexShape.up ℕ)

/-- The positive-degree stagewise cohomology comparisons, assembled as a
natural isomorphism of filtered diagrams. -/
@[expose] noncomputable def filteredFlasquePositiveIsoSectionsHomologyDiagram
    (q : ℕ) (hq : 0 < q) :
    F ⋙ CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) q ≅
      filteredFlasqueResolutionSectionsDiagram F ⋙
        HomologicalComplex.homologyFunctor
          AddCommGrpCat (ComplexShape.up ℕ) q :=
  NatIso.ofComponents
    (fun i => (flasqueAcyclicResolution (F.obj i)).positiveIsoSectionsHomology q hq)
    (fun {i j} f => by
      exact
        (flasqueAcyclicResolution (F.obj i)).positiveIsoSectionsHomology_hom_naturality
          (flasqueAcyclicResolution (F.obj j))
          (flasqueAcyclicResolutionHom (F.map f)) q hq)

local instance filteredFlasqueResolution_sections_additive :
    ((SheafCohomology.CompactOpenSections.sections
      (X := X) (⊤ : Opens X) :
        Sheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0})).Additive where
  map_add := by
    intros
    rfl

noncomputable instance filteredFlasqueResolutionTerm_preservesColimit_sections
    (n : ℕ) : PreservesColimit
      ((filteredFlasqueResolutionComplexDiagram F).X n)
      (SheafCohomology.CompactOpenSections.sections
        (X := X) (⊤ : Opens X)) :=
  SheafCohomology.CompactOpenSections.preservesColimit_globalSections _

/-- Terminal sections commute with the degreewise filtered colimit of the
stagewise flasque resolutions. -/
noncomputable abbrev filteredFlasqueResolutionSectionsIso :=
  let G : Sheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0} :=
    SheafCohomology.CompactOpenSections.sections
      (X := X) (⊤ : Opens X)
  letI : G.Additive := by
    dsimp only [G]
    exact filteredFlasqueResolution_sections_additive (X := X)
  HomologicalComplex.colimMapIso G
    (filteredFlasqueResolutionComplexDiagram F)

/-- The positive-degree comparison from the colimit of stagewise cohomology
to the cohomology of the colimit sheaf. -/
@[expose] noncomputable def filteredFlasquePositiveColimitIso
    (q : ℕ) (hq : 0 < q) :=
  (colim (J := I) (C := AddCommGrpCat)).mapIso
      (filteredFlasquePositiveIsoSectionsHomologyDiagram F q hq) ≪≫
    HomologicalComplex.homologyColimitIso
      (filteredFlasqueResolutionSectionsDiagram F) q ≪≫
    HomologicalComplex.homologyMapIso
      (HomologicalComplex.ofFunctorColimIso
        (filteredFlasqueResolutionSectionsDiagram F)).symm q ≪≫
    HomologicalComplex.homologyMapIso
      (filteredFlasqueResolutionSectionsIso F) q ≪≫
    ((filteredFlasqueAcyclicResolution F).positiveIsoSectionsHomology q hq).symm

omit [HasExt (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{0})] in
set_option backward.isDefEq.respectTransparency false in
theorem ofFunctorColimitι_comp_filteredFlasqueResolutionSectionsIso_hom
    (i : I) :
    HomologicalComplex.ofFunctorColimitι
        (filteredFlasqueResolutionSectionsDiagram F) i ≫
      (filteredFlasqueResolutionSectionsIso F).hom =
    ((SheafCohomology.CompactOpenSections.sections
      (X := X) (⊤ : Opens X)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (filteredFlasqueResolutionι F i) := by
  apply HomologicalComplex.Hom.ext
  funext n
  dsimp only [filteredFlasqueResolutionSectionsIso,
    HomologicalComplex.colimMapIso, asIso_hom,
    HomologicalComplex.colimMapComparison,
    HomologicalComplex.ofFunctorColimitι]
  change
    colimit.ι ((filteredFlasqueResolutionComplexDiagram F).X n ⋙
        (SheafCohomology.CompactOpenSections.sections
          (X := X) (⊤ : Opens X))) i ≫
      colimit.post ((filteredFlasqueResolutionComplexDiagram F).X n)
        (SheafCohomology.CompactOpenSections.sections
          (X := X) (⊤ : Opens X)) = _
  rw [colimit.ι_post]
  simp [filteredFlasqueResolutionι,
    filteredFlasqueResolutionComplexColimitι,
    filteredFlasqueResolutionComplexDiagramEvalIso]
  rfl

omit [HasExt (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{0})] in
set_option backward.isDefEq.respectTransparency false in
theorem colimitι_comp_ofFunctorColimIso_inv_comp_sectionsIso_hom
    (i : I) :
    colimit.ι (filteredFlasqueResolutionSectionsDiagram F) i ≫
        (HomologicalComplex.ofFunctorColimIso
          (filteredFlasqueResolutionSectionsDiagram F)).inv ≫
      (filteredFlasqueResolutionSectionsIso F).hom =
    ((SheafCohomology.CompactOpenSections.sections
      (X := X) (⊤ : Opens X)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (filteredFlasqueResolutionι F i) := by
  rw [← Category.assoc]
  rw [show
    colimit.ι (filteredFlasqueResolutionSectionsDiagram F) i ≫
        (HomologicalComplex.ofFunctorColimIso
          (filteredFlasqueResolutionSectionsDiagram F)).inv =
      HomologicalComplex.ofFunctorColimitι
        (filteredFlasqueResolutionSectionsDiagram F) i by
    apply (Iso.comp_inv_eq _).2
    exact (HomologicalComplex.ofFunctorColimitι_comp_ofFunctorColimIso_hom
        (filteredFlasqueResolutionSectionsDiagram F) i).symm]
  exact ofFunctorColimitι_comp_filteredFlasqueResolutionSectionsIso_hom F i

set_option backward.isDefEq.respectTransparency false in
/-- The constructed positive-degree isomorphism is the canonical comparison
map from the colimit of the values to the value on the colimit. -/
theorem filteredFlasquePositiveColimitIso_hom
    (q : ℕ) (hq : 0 < q) :
    (filteredFlasquePositiveColimitIso F q hq).hom =
      colimit.post F (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) q) := by
  apply colimit.hom_ext
  intro i
  rw [colimit.ι_post]
  dsimp only [filteredFlasquePositiveColimitIso, Iso.trans_hom,
    Functor.mapIso_hom]
  rw [← Category.assoc]
  change
    (colimit.ι (F ⋙ CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) q) i ≫
      colimMap (filteredFlasquePositiveIsoSectionsHomologyDiagram
        F q hq).hom) ≫ _ = _
  rw [ι_colimMap]
  simp only [Category.assoc]
  rw [HomologicalComplex.homologyColimitIso_hom_ι_assoc]
  change
    ((flasqueAcyclicResolution (F.obj i)).positiveIsoSectionsHomology q hq).hom ≫
      HomologicalComplex.homologyMap
        (colimit.ι (filteredFlasqueResolutionSectionsDiagram F) i) q ≫
      HomologicalComplex.homologyMap
        (HomologicalComplex.ofFunctorColimIso
          (filteredFlasqueResolutionSectionsDiagram F)).inv q ≫
      HomologicalComplex.homologyMap
        (filteredFlasqueResolutionSectionsIso F).hom q ≫
      ((filteredFlasqueAcyclicResolution F).positiveIsoSectionsHomology q hq).inv = _
  have hmaps :
      HomologicalComplex.homologyMap
          (colimit.ι (filteredFlasqueResolutionSectionsDiagram F) i) q ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex.ofFunctorColimIso
            (filteredFlasqueResolutionSectionsDiagram F)).inv q ≫
        HomologicalComplex.homologyMap
          (filteredFlasqueResolutionSectionsIso F).hom q =
      HomologicalComplex.homologyMap
        (((SheafCohomology.CompactOpenSections.sections
          (X := X) (⊤ : Opens X)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map (filteredFlasqueResolutionι F i)) q := by
    rw [← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp]
    rw [colimitι_comp_ofFunctorColimIso_inv_comp_sectionsIso_hom]
  rw [reassoc_of% hmaps]
  change
    ((flasqueAcyclicResolution (F.obj i)).positiveIsoSectionsHomology q hq).hom ≫
      HomologicalComplex.homologyMap
        (((SheafCohomology.CompactOpenSections.sections
          (X := X) (⊤ : Opens X)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map
          (filteredFlasqueAcyclicResolutionHom F i).hom) q ≫
      ((filteredFlasqueAcyclicResolution F).positiveIsoSectionsHomology q hq).inv = _
  rw [← (flasqueAcyclicResolution (F.obj i)).positiveIsoSectionsHomology_hom_naturality_assoc
      (filteredFlasqueAcyclicResolution F)
      (filteredFlasqueAcyclicResolutionHom F i) q hq]
  simp

/-- Positive-degree sheaf cohomology preserves same-size filtered colimits on
a compact prespectral quasi-separated space. -/
theorem preservesColimit_functorH_positive (q : ℕ) (hq : 0 < q) :
    PreservesColimit F (CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology X) q) := by
  let _ : IsIso (colimit.post F (CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology X) q)) :=
    (filteredFlasquePositiveColimitIso_hom (X := X) (hExt := hExt)
      (I := I) F q hq) ▸
      (inferInstance : IsIso
        (filteredFlasquePositiveColimitIso (X := X) (hExt := hExt)
          (I := I) F q hq).hom)
  exact preservesColimit_of_isIso_post _ F

/-- Sheaf cohomology in every degree preserves same-size filtered colimits on
a compact prespectral quasi-separated space. -/
theorem preservesColimit_functorH (q : ℕ) :
    PreservesColimit F (CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology X) q) := by
  rcases q with _ | q
  · exact SheafCohomology.DegreeZero.preservesColimit_functorH_zero
      (X := X) F
  · exact preservesColimit_functorH_positive (X := X) (I := I)
      F (q + 1) (by omega)

end TopCat.Sheaf
