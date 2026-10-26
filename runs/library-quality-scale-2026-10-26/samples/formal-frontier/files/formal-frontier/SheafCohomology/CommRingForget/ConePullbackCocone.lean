/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Adapted from SheafCohomology.AbelianForget.ConePullbackCocone by Anchor (source maintainer).
-/


module
public import SheafCohomology.CommRingForget.ConePullback
public import SheafCohomology.ConePullbackCocone

public section

/-!
# Forgetting the native inverse-image cocone

For a cone of ring sheafed spaces, the native Type-valued projection mates
agree with the forgotten ring projection mates after the canonical pullback
comparison. No assumption that either cocone is colimiting is needed.

Ring adaptation: Formal Frontier Agents. The original additive work
is credited to Anchor. Expression and proof outline
adapt published `SheafCohomology.AbelianForget.ConePullbackCocone` at official revision
`e4c7d681e0913fc1dde266cfcfc37763f1d47785` (Anchor);
native cone/limit and generic category-theoretic APIs are imported, not copied.
-/

set_option warningAsError true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopCat.Sheaf.CommRingForget

universe v vj wj

namespace AlgebraicGeometry.SheafedSpace.CommRingForget

variable {J : Type wj} [Category.{vj} J]

/-- Mapping an actual native cone through the underlying sheafed-space functor
agrees strictly with forgetting its ring mapped cone. -/
theorem underlying_mapCone_forget (S : Jᵒᵖ ⥤ SheafedSpace CommRingCat.{v})
    (c : Cone S) :
    (SheafedSpace.forget (Type v)).mapCone (underlying.mapCone c) =
      underlyingCone S ((SheafedSpace.forget CommRingCat.{v}).mapCone c) := by
  rfl

/-- The Type-valued leg of the actual native cone is precisely the ring
projection mate transported along the canonical pullback comparison. -/
theorem conePullbackCocone_forget_ι (S : Jᵒᵖ ⥤ SheafedSpace CommRingCat.{v})
    (c : Cone S) (i : J) :
    (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying) (underlying.mapCone c)).ι.app i =
      (conePullbackIso S ((SheafedSpace.forget CommRingCat.{v}).mapCone c)).hom.app i ≫
        (underlyingSheaf (c.pt : TopCat)).map
          ((SheafedSpace.conePullbackCocone CommRingCat.{v} S c).ι.app i) := by
  rw [SheafedSpace.conePullbackCocone_ι_app,
    SheafedSpace.conePullbackCocone_ι_app, conePullbackIso_hom_app]
  exact underlying_sheafMate (c.π.app (op i))

end AlgebraicGeometry.SheafedSpace.CommRingForget
