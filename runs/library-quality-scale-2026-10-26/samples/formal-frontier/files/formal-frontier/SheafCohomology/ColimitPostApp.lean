/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

public section

set_option warningAsError true

/-!
# Components of canonical colimit maps

This identifies a component of the canonical `colimit.post` for a
functor-category-valued functor with the
canonical comparison after evaluation, including the unavoidable associator
and pointwise-colimit isomorphisms. It then reduces componentwise invertibility
to preservation of the original colimit by the evaluated functor.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe vJ uJ vC uC vK uK vD uD

namespace SheafCohomology.HigherDirectImageFilteredColimit

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable {K : Type uK} [Category.{vK} K]
variable {D : Type uD} [Category.{vD} D]

theorem colimit_post_app_eq
    (F : J ⥤ C) (L : C ⥤ K ⥤ D) (k : K)
    [HasColimit F] [HasColimitsOfShape J D] :
    (colimit.post F L).app k =
      (colimitObjIsoColimitCompEvaluation (F ⋙ L) k).hom ≫
        (HasColimit.isoOfNatIso
          (Functor.associator F L ((evaluation K D).obj k))).hom ≫
        colimit.post F (L ⋙ (evaluation K D).obj k) := by
  apply colimit_obj_ext
  intro j
  change (colimit.ι (F ⋙ L) j ≫ colimit.post F L).app k = _
  rw [colimit.ι_post]
  rw [← Category.assoc, colimitObjIsoColimitCompEvaluation_ι_app_hom]
  rw [← Category.assoc, HasColimit.ι_isoOfNatIso_hom]
  simp only [Functor.associator_hom_app, Category.id_comp, colimit.ι_post]
  rfl

theorem colimit_post_app_isIso_of_preserves
    (F : J ⥤ C) (L : C ⥤ K ⥤ D) (k : K)
    [HasColimit F] [HasColimitsOfShape J D]
    [PreservesColimit F (L ⋙ (evaluation K D).obj k)] :
    IsIso ((colimit.post F L).app k) := by
  rw [colimit_post_app_eq]
  infer_instance

#print axioms colimit_post_app_eq
#print axioms colimit_post_app_isIso_of_preserves

end SheafCohomology.HigherDirectImageFilteredColimit
