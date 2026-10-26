/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import Mathlib.CategoryTheory.Limits.HasLimits

public section

set_option warningAsError true

/-!
# Transport of canonical colimit maps

This generic stage-leg lemma shows that a
natural transformation carries the canonical `colimit.post` comparison to the
canonical comparison for the target functor.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe vJ uJ vC uC vD uD

namespace SheafCohomology.HigherDirectImageFilteredColimit

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- The canonical colimit comparison commutes with change of the target
functor by a natural transformation. -/
theorem colimMap_whiskerLeft_comp_colimit_post
    (F : J ⥤ C) (L R : C ⥤ D) (α : L ⟶ R)
    [HasColimit F] [HasColimit (F ⋙ L)] [HasColimit (F ⋙ R)] :
    colimMap (Functor.whiskerLeft F α) ≫ colimit.post F R =
      colimit.post F L ≫ α.app (colimit F) := by
  apply colimit.hom_ext
  intro j
  rw [← Category.assoc, ι_colimMap, Category.assoc, colimit.ι_post,
    colimit.ι_post_assoc]
  exact (α.naturality (colimit.ι F j)).symm

#print axioms colimMap_whiskerLeft_comp_colimit_post

end SheafCohomology.HigherDirectImageFilteredColimit
