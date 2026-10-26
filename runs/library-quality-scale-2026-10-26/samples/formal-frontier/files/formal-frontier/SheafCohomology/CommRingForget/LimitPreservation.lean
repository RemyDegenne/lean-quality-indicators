/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Adapted from SheafCohomology.AbelianForget.LimitPreservation by Formal Frontier Agents.
-/


module
public import SheafCohomology.CommRingForget.FilteredColimits
public import SheafCohomology.CommRingForget.ConePullbackCocone
public import SheafCohomology.LimitConstruction
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.Topology.Category.TopCat.Limits.Basic

public section

/-!
# Cofiltered limits of ring sheafed spaces after forgetting coefficients

For a same-universe filtered index category `J`, forgetting the commutative-ring
structure of the sheaves preserves the native limit of a diagram indexed by
`Jᵒᵖ`. The proof uses the accepted native cone construction and its actual
projection-mate cocone, and the filtered-colimit theorem for sheaves on the
underlying space. The index must be filtered: forgetting ring structure
does not generally preserve the initial sheaf of an empty native limit.

Original additive proof: Formal Frontier Agents; see its shipped header and
`docs/CREDITS.md` for contributor and adaptation context.

Ring adaptation: Formal Frontier Agents; the expression and proof outline
closely adapt the separately credited original additive proof
in published `SheafCohomology.AbelianForget.LimitPreservation` at official revision
`e4c7d681e0913fc1dde266cfcfc37763f1d47785` (Formal Frontier Agents);
native cone/limit and generic category-theoretic APIs are imported, not copied.
-/

set_option warningAsError true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopCat.Sheaf.CommRingForget

universe v

namespace AlgebraicGeometry.SheafedSpace.CommRingForget

variable {J : Type v} [SmallCategory J] [IsFiltered J]

/-- Forgetting coefficients and transporting the inverse-image diagram preserves
the colimit of the actual projection-mate cocone of an ring native cone. -/
noncomputable def isColimit_conePullbackCocone_underlying
    (S : Jᵒᵖ ⥤ SheafedSpace CommRingCat.{v}) (C : Cone S)
    (hK : IsColimit (SheafedSpace.conePullbackCocone CommRingCat.{v} S C)) :
    IsColimit (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
      (underlying.mapCone C)) := by
  let D := SheafedSpace.conePullback CommRingCat.{v} S
    ((SheafedSpace.forget CommRingCat.{v}).mapCone C)
  let F := underlyingSheaf (C.pt : TopCat)
  have hMapped : IsColimit
      (F.mapCocone (SheafedSpace.conePullbackCocone CommRingCat.{v} S C)) :=
    Classical.choice ((preservesFilteredSheafColimit (C.pt : TopCat) D).preserves hK)
  have hPre := (IsColimit.precomposeHomEquiv
    (conePullbackIso S ((SheafedSpace.forget CommRingCat.{v}).mapCone C)) _).symm hMapped
  refine hPre.ofIsoColimit (Cocone.ext (Iso.refl _) (fun i ↦ ?_))
  change (conePullbackIso S ((SheafedSpace.forget CommRingCat.{v}).mapCone C)).hom.app i ≫
      (underlyingSheaf (C.pt : TopCat)).map
        ((SheafedSpace.conePullbackCocone CommRingCat.{v} S C).ι.app i) =
      (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
        (underlying.mapCone C)).ι.app i
  exact (conePullbackCocone_forget_ι S C i).symm

/-- A constructed native limit above a given limiting space cone remains
limiting after forgetting the commutative-ring structure of its sheaf. -/
theorem preservesLimit_fromSpaceCone
    (S : Jᵒᵖ ⥤ SheafedSpace CommRingCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget CommRingCat.{v})) (hc : IsLimit c)
    [HasWeakSheafify (Opens.grothendieckTopology c.pt) CommRingCat.{v}] :
    PreservesLimit S underlying := by
  let K := SheafedSpace.conePullbackColimitCocone CommRingCat.{v} S c
  let C := (SheafedSpace.limitConeOfSpaceCone CommRingCat.{v} S c hc).cone
  have hK : IsColimit K :=
    SheafedSpace.conePullbackColimitCocone_isColimit CommRingCat.{v} S c
  have hC : IsColimit (SheafedSpace.conePullbackCocone CommRingCat.{v} S C) := by
    change IsColimit (SheafedSpace.conePullbackCocone CommRingCat.{v} S
      (SheafedSpace.coneOfPullbackCocone CommRingCat.{v} S c K))
    refine hK.ofIsoColimit (Cocone.ext (Iso.refl _) (fun i ↦ ?_))
    change K.ι.app i = SheafedSpace.sheafMate CommRingCat.{v}
      ((SheafedSpace.coneOfPullbackCocone CommRingCat.{v} S c K).π.app (op i))
    exact (SheafedSpace.coneOfPullbackCocone_π_mate CommRingCat.{v}
      S c K (op i)).symm
  have hBase : IsLimit ((SheafedSpace.forget (Type v)).mapCone
      (underlying.mapCone C)) := by
    rw [underlying_mapCone_forget S C]
    rw [SheafedSpace.limitConeOfSpaceCone_forget CommRingCat.{v} S c hc]
    exact hc
  have hSheaf := isColimit_conePullbackCocone_underlying S C hC
  have hType : IsLimit (underlying.mapCone C) :=
    SheafedSpace.isLimit_of_isLimit_forget_of_isColimit_conePullbackCocone
      (Type v) (S ⋙ underlying) (underlying.mapCone C) hBase hSheaf
  exact preservesLimit_of_preserves_limit_cone
    (SheafedSpace.limitConeOfSpaceCone CommRingCat.{v} S c hc).isLimit hType

/-- The native coefficient-forgetting functor preserves every same-universe
cofiltered limit of ring sheafed spaces indexed by `Jᵒᵖ`. -/
theorem preservesCofilteredLimit
    (S : Jᵒᵖ ⥤ SheafedSpace CommRingCat.{v}) : PreservesLimit S underlying := by
  let c : Cone (S ⋙ SheafedSpace.forget CommRingCat.{v}) :=
    limit.cone (S ⋙ SheafedSpace.forget CommRingCat.{v})
  let hc : IsLimit c := limit.isLimit (S ⋙ SheafedSpace.forget CommRingCat.{v})
  exact preservesLimit_fromSpaceCone S c hc

/-- A named shape-level witness, without a global preservation instance. -/
theorem preservesCofilteredLimitsOfShape :
    PreservesLimitsOfShape Jᵒᵖ underlying.{v} :=
  ⟨fun {S} ↦ preservesCofilteredLimit S⟩

end AlgebraicGeometry.SheafedSpace.CommRingForget
