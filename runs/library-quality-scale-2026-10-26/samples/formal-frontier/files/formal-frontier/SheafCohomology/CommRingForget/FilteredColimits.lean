/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Adapted from SheafCohomology.AbelianForget.FilteredColimits by Anchor (source maintainer).
-/


module
public import SheafCohomology.CommRingForget.Basic
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

public section

/-!
# Filtered colimits of underlying commutative-ring sheaves

For a same-universe small filtered diagram, the native underlying-sheaf functor
preserves its colimit. The canonical comparison is the literal `colimit.post`.

Ring adaptation: Formal Frontier Agents. Original additive authorship
remains with Anchor; this proof structure adapts
the published additive file `SheafCohomology.AbelianForget.FilteredColimits`
from official revision `e4c7d681e0913fc1dde266cfcfc37763f1d47785`
(Anchor, source maintainer); generic sheafification and colimit APIs are mathlib.
-/

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace

universe v

namespace TopCat.Sheaf.CommRingForget

variable (Z : TopCat.{v}) {I : Type v} [SmallCategory I]

private abbrev J := Opens.grothendieckTopology Z
private abbrev H := (whiskeringRight (Opens Z)ᵒᵖ CommRingCat.{v} (Type v)).obj
  (CategoryTheory.forget CommRingCat.{v})

private def comparisonIso :
    H Z ⋙ presheafToSheaf (J Z) (Type v) ≅
      presheafToSheaf (J Z) CommRingCat.{v} ⋙ underlyingSheaf Z :=
  sheafComposeNatIso (J Z) (CategoryTheory.forget CommRingCat.{v})
    (sheafificationAdjunction (J Z) CommRingCat.{v})
    (sheafificationAdjunction (J Z) (Type v))

private theorem presheafPreservation [IsFiltered I] : PreservesColimitsOfShape I
    (presheafToSheaf (J Z) CommRingCat.{v} ⋙ underlyingSheaf Z) := by
  have hWhisker : PreservesColimitsOfShape I (H Z) := inferInstance
  have hSheafify : PreservesColimitsOfShape I (presheafToSheaf (J Z) (Type v)) :=
    inferInstance
  have hComp : PreservesColimitsOfShape I (H Z ⋙ presheafToSheaf (J Z) (Type v)) :=
    @comp_preservesColimitsOfShape _ _ _ _ _ _ _ _ (H Z)
      (presheafToSheaf (J Z) (Type v)) hWhisker hSheafify
  exact @preservesColimitsOfShape_of_natIso _ _ _ _ _ _ _ _ (comparisonIso Z) hComp

variable (D : I ⥤ Z.Sheaf CommRingCat.{v})

/-- Forgetting commutative-ring structure preserves the colimit of every
same-universe filtered diagram of sheaves on `Z`. -/
theorem preservesFilteredSheafColimit [IsFiltered I] :
    PreservesColimit D (underlyingSheaf Z) := by
  let P := D ⋙ sheafToPresheaf (J Z) CommRingCat.{v}
  let E := colimit.cocone P
  have hE : IsColimit E := colimit.isColimit P
  let T := CategoryTheory.Sheaf.sheafifyCocone E
  have hT : IsColimit T := CategoryTheory.Sheaf.isColimitSheafifyCocone E hE
  have hFun : PreservesColimit P
      (presheafToSheaf (J Z) CommRingCat.{v} ⋙ underlyingSheaf Z) :=
    (presheafPreservation Z).preservesColimit
  have hU : IsColimit
      ((presheafToSheaf (J Z) CommRingCat.{v} ⋙ underlyingSheaf Z).mapCocone E) :=
    Classical.choice (hFun.preserves hE)
  have hTop : IsColimit ((underlyingSheaf Z).mapCocone T) := by
    have hU' : IsColimit ((underlyingSheaf Z).mapCocone
        ((presheafToSheaf (J Z) CommRingCat.{v}).mapCocone E)) :=
      hU.ofIsoColimit (Functor.mapCoconeMapCocone E).symm
    let α : D ≅ P ⋙ presheafToSheaf (J Z) CommRingCat.{v} :=
      Functor.isoWhiskerLeft D (asIso (sheafificationAdjunction (J Z)
        CommRingCat.{v}).counit).symm
    have hpre : IsColimit ((Cocone.precompose (whiskerRight α.hom (underlyingSheaf Z))).obj
        ((underlyingSheaf Z).mapCocone
          ((presheafToSheaf (J Z) CommRingCat.{v}).mapCocone E))) :=
      (IsColimit.precomposeHomEquiv (Functor.isoWhiskerRight α (underlyingSheaf Z)) _).symm hU'
    exact hpre.ofIsoColimit (Functor.mapCoconePrecompose (underlyingSheaf Z)).symm
  exact preservesColimit_of_preserves_colimit_cocone hT hTop

/-- A convenient preservation witness for all diagrams of a fixed filtered shape. -/
theorem preservesFilteredColimits [IsFiltered I] :
    PreservesColimitsOfShape I (underlyingSheaf Z) :=
  ⟨fun {D} => preservesFilteredSheafColimit Z D⟩

/-- The literal `colimit.post` comparison satisfies the native stage-leg law. -/
theorem canonicalComparison_stage [HasColimit D] [HasColimit (D ⋙ underlyingSheaf Z)] (i : I) :
    colimit.ι (D ⋙ underlyingSheaf Z) i ≫ colimit.post D (underlyingSheaf Z) =
      (underlyingSheaf Z).map (colimit.ι D i) :=
  colimit.ι_post D (underlyingSheaf Z) i

/-- The literal `colimit.post` is invertible for every filtered diagram of
commutative-ring sheaves on `Z`. -/
theorem canonicalComparison_isIso [IsFiltered I] [HasColimit D]
    [HasColimit (D ⋙ underlyingSheaf Z)] :
    IsIso (colimit.post D (underlyingSheaf Z)) := by
  have h : IsColimit ((underlyingSheaf Z).mapCocone (colimit.cocone D)) :=
    Classical.choice ((preservesFilteredSheafColimit Z D).preserves (colimit.isColimit D))
  let comparisonIso := h.coconePointUniqueUpToIso (colimit.isColimit (D ⋙ underlyingSheaf Z))
  have heq : comparisonIso.inv = colimit.post D (underlyingSheaf Z) := by
    apply colimit.hom_ext
    intro i
    exact (h.comp_coconePointUniqueUpToIso_inv
      (colimit.isColimit (D ⋙ underlyingSheaf Z)) i).trans
        (canonicalComparison_stage Z D i).symm
  rw [← heq]
  infer_instance


end TopCat.Sheaf.CommRingForget
