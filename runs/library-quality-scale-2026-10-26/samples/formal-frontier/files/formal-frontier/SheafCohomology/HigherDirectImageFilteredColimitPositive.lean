/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import SheafCohomology.SheafificationBasis
public import SheafCohomology.SpectralPreimage
public import SheafCohomology.ColimitPostApp
public import SheafCohomology.ColimitTransport
public import SheafCohomology.LocalCohomologyFilteredColimit
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import SheafCohomology.OpenCohomologyRightDerived

public section

set_option warningAsError true

/-!
# Positive higher direct images preserve filtered colimits

This assembles the compact-basic
calculation into preservation of a same-small-universe filtered colimit by
sheafified local cohomology, then transports the result to positive-degree
right-derived pushforward.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace SheafCohomology.HigherDirectImageFilteredColimit

open TopCat.Sheaf

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
variable [PrespectralSpace X] [QuasiSeparatedSpace X]
variable [PrespectralSpace Y]
variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
variable [HasSheafify
  (Opens.grothendieckTopology Y) AddCommGrpCat.{0}]
variable [HasExt.{0} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{0})]
variable {I : Type} [SmallCategory I]
variable (F : I ⥤ X.Sheaf AddCommGrpCat.{0})

section Filtered

variable [IsFiltered I]

omit [PrespectralSpace Y]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{0}] in
/-- At a compact open of the target, the canonical comparison for the local
cohomology presheaf is an isomorphism. -/
theorem localCohomologyPresheaf_colimitPost_app_isIso
    (hf : IsSpectralMap f) (q : ℕ) (V : Opens Y)
    (hV : IsCompact (V : Set Y)) :
    IsIso ((colimit.post F (localCohomologyPresheafFunctor f q)).app
      (.op V)) := by
  let U : Opens X := (Opens.map f).obj V
  let _ : PrespectralSpace U := preimagePrespectralSpace hf V
  let _ : CompactSpace U := preimageCompactSpace hf V hV
  let _ : QuasiSeparatedSpace U := preimageQuasiSeparatedSpace hf V
  let _ : HasExt.{0} (CategoryTheory.Sheaf
      ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{0}) :=
    CategoryTheory.IsGrothendieckAbelian.hasExt _
  let _ : HasExt.{0} (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{0}) :=
    CategoryTheory.IsGrothendieckAbelian.hasExt _
  have hpres : PreservesColimit F
      (localCohomologyPresheafFunctor f q ⋙
        (evaluation _ _).obj (.op V)) := by
    change PreservesColimit F
      (CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) q ⋙
        (evaluation _ _).obj (.op U))
    exact cohomologyPresheafEvaluation_preservesColimit U F q
  let _ := hpres
  exact colimit_post_app_isIso_of_preserves F
    (localCohomologyPresheafFunctor f q) (.op V)

omit [HasSheafify
  (Opens.grothendieckTopology Y) AddCommGrpCat.{0}] in
/-- Sheafifying the canonical local-cohomology-presheaf comparison produces
an isomorphism, because it is already an isomorphism on the compact-open basis
of the prespectral target. -/
theorem sheafifiedLocalCohomology_colimitPost_map_isIso
    (hf : IsSpectralMap f) (q : ℕ) :
    IsIso ((presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{0}).map
        (colimit.post F (localCohomologyPresheafFunctor f q))) := by
  apply presheafToSheaf_map_isIso_of_isBasis
    (PrespectralSpace.isBasis_opens Y)
  intro V hV
  exact localCohomologyPresheaf_colimitPost_app_isIso f F hf q V hV

/-- Sheafified local cohomology preserves a same-small-universe filtered
colimit along a spectral map into a prespectral target. -/
theorem sheafifiedLocalCohomology_preservesColimit
    (hf : IsSpectralMap f) (q : ℕ) :
    PreservesColimit F (sheafifiedLocalCohomologyFunctor f q) := by
  let L := localCohomologyPresheafFunctor f q
  let S := presheafToSheaf (Opens.grothendieckTopology Y)
    AddCommGrpCat.{0}
  let κ := colimit.post F L
  let _ : IsIso (S.map κ) := by
    exact sheafifiedLocalCohomology_colimitPost_map_isIso f F hf q
  let _ : PreservesColimitsOfSize.{0, 0} S := inferInstance
  let _ : IsIso (colimit.post (F ⋙ L) S) := inferInstance
  let _ : IsIso (colimit.post F (L ⋙ S)) := by
    rw [← colimit.post_post]
    infer_instance
  exact preservesColimit_of_isIso_post (L ⋙ S) F

/-- In positive degree, right-derived pushforward preserves the same filtered
colimit, through the accepted natural comparison with sheafified local
cohomology. -/
theorem rightDerivedPushforward_preservesColimit_positive
    (hf : IsSpectralMap f) (q : ℕ) (hq : 0 < q) :
    PreservesColimit F
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived q) :=
  (preservesColimit_iff_of_natIso F
    (TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyFunctorIsoRightDerived
      f q hq)).mp
        (sheafifiedLocalCohomology_preservesColimit f F hf q)

end Filtered

omit [PrespectralSpace X] [QuasiSeparatedSpace X]
  [PrespectralSpace Y] in
/-- The canonical comparison for sheafified local cohomology is literally the
sheafification of the canonical presheaf comparison, preceded by the canonical
comparison expressing that sheafification preserves the presheaf colimit. -/
theorem localCohomologyPresheaf_colimitPost_sheafification_factorization
    (q : ℕ) :
    let L := localCohomologyPresheafFunctor f q
    let S := presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{0}
    colimit.post (F ⋙ L) S ≫ S.map (colimit.post F L) =
      colimit.post F (sheafifiedLocalCohomologyFunctor f q) := by
  dsimp only
  exact colimit.post_post F _ _

omit [PrespectralSpace X] [QuasiSeparatedSpace X]
  [PrespectralSpace Y] in
/-- The canonical comparison for sheafified local cohomology transports to
the literal canonical comparison for positive-degree right-derived
pushforward. The equality is proved on every colimit cocone leg. -/
theorem sheafifiedLocalCohomology_colimitPost_transport_rightDerived
    (q : ℕ) (hq : 0 < q) :
    let e :=
      TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyFunctorIsoRightDerived
        f q hq
    colimMap (Functor.whiskerLeft F e.hom) ≫
        colimit.post F
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived q) =
      colimit.post F (sheafifiedLocalCohomologyFunctor f q) ≫
        e.hom.app (colimit F) := by
  dsimp only
  exact colimMap_whiskerLeft_comp_colimit_post F _ _ _

omit [PrespectralSpace X] [QuasiSeparatedSpace X]
  [PrespectralSpace Y] in
/-- The sheafification of the canonical local-cohomology-presheaf comparison,
including the canonical sheafification/colimit comparison, is exactly the
positive right-derived canonical comparison after transport by the accepted
natural isomorphism on the source and target. -/
theorem localCohomologyPresheaf_colimitPost_factorization_rightDerived
    (q : ℕ) (hq : 0 < q) :
    let L := localCohomologyPresheafFunctor f q
    let S := presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{0}
    let e :=
      TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyFunctorIsoRightDerived
        f q hq
    (colimit.post (F ⋙ L) S ≫
          S.map (colimit.post F L)) ≫ e.hom.app (colimit F) =
      colimMap (Functor.whiskerLeft F e.hom) ≫
        colimit.post F
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived q) := by
  dsimp only
  rw [localCohomologyPresheaf_colimitPost_sheafification_factorization]
  exact (sheafifiedLocalCohomology_colimitPost_transport_rightDerived
    f F q hq).symm

#print axioms localCohomologyPresheaf_colimitPost_app_isIso
#print axioms sheafifiedLocalCohomology_colimitPost_map_isIso
#print axioms sheafifiedLocalCohomology_preservesColimit
#print axioms rightDerivedPushforward_preservesColimit_positive
#print axioms localCohomologyPresheaf_colimitPost_sheafification_factorization
#print axioms sheafifiedLocalCohomology_colimitPost_transport_rightDerived
#print axioms localCohomologyPresheaf_colimitPost_factorization_rightDerived

end SheafCohomology.HigherDirectImageFilteredColimit
