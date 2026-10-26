/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import SheafCohomology.LimitConstruction
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

public section

/-!
# Preservation of native sheafed-space limits by the space forgetful functor

The native limit constructed over an actual limiting space cone maps to that
entire cone. Mathlib's single-cone criterion therefore supplies the ordinary
`PreservesLimit` API for every limiting cone of the same diagram.
-/

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w u vj wj

namespace AlgebraicGeometry.SheafedSpace

variable (A : Type u) [Category.{w} A]
variable {FA : A → A → Type*} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
variable [ConcreteCategory.{w} A FA] [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]
variable {J : Type wj} [Category.{vj} J] [HasColimitsOfShape J A]

include FA CA

/-- Forgetting sheafed spaces preserves a diagram's limit when an actual limiting
space cone admits the native limit construction over its vertex. -/
theorem preservesLimitForgetOfSpaceCone (S : Jᵒᵖ ⥤ SheafedSpace.{u,w,w} A)
    (c : Cone (S ⋙ forget A)) (hc : IsLimit c)
    [HasWeakSheafify (Opens.grothendieckTopology c.pt) A] :
    PreservesLimit S (forget A) := by
  let native : LimitCone S := limitConeOfSpaceCone (FA := FA) (CA := CA) A S c hc
  have hmap : IsLimit ((forget A).mapCone native.cone) := by
    change IsLimit ((forget A).mapCone
      (limitConeOfSpaceCone (FA := FA) (CA := CA) A S c hc).cone)
    rw [limitConeOfSpaceCone_forget]
    exact hc
  exact preservesLimit_of_preserves_limit_cone native.isLimit hmap

/-- A chosen limit of the space diagram and sheafification at its vertex give a
named preservation witness, without registering an instance for all diagrams. -/
theorem preservesLimitForgetOfHasLimit (S : Jᵒᵖ ⥤ SheafedSpace.{u,w,w} A)
    [HasLimit (S ⋙ forget A)]
    [HasWeakSheafify (Opens.grothendieckTopology
      ((limit (S ⋙ forget A)) : TopCat)) A] :
    PreservesLimit S (forget A) := by
  let c : Cone (S ⋙ forget A) := limit.cone (S ⋙ forget A)
  let hc : IsLimit c := limit.isLimit (S ⋙ forget A)
  exact preservesLimitForgetOfSpaceCone (FA := FA) (CA := CA) A S c hc

end AlgebraicGeometry.SheafedSpace
