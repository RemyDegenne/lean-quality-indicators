/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import Mathlib.Topology.Category.CompHaus.Basic

public section

/-!
# Compact Hausdorff limits of topological modules

This file transfers compact Hausdorff structure from every object of a small
diagram of topological modules to its categorical limit.  The construction
views the same diagram in `CompHaus`, then compares the two limits through the
forgetful functors to `TopCat`.

The results are explicit theorem values rather than global instances.  A
downstream application can install them locally after proving compactness and
Hausdorffness of its stages, without introducing instance-search loops.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace TopModuleCat

variable {J : Type v} [SmallCategory J]
variable {R : Type u} [Ring R] [TopologicalSpace R]
variable (F : J ⥤ TopModuleCat.{max u v} R)

/-- A diagram of compact Hausdorff spaces obtained by forgetting the module
structure from a diagram of compact Hausdorff topological modules. -/
noncomputable def compHausDiagram
    [∀ j, CompactSpace (F.obj j)] [∀ j, T2Space (F.obj j)] :
    J ⥤ CompHaus.{max u v} where
  obj j := CompHaus.of (F.obj j)
  map f := InducedCategory.homMk
    ((forget₂ (TopModuleCat.{max u v} R) TopCat.{max u v}).map (F.map f))

/-- The canonical homeomorphism from the underlying space of a
`TopModuleCat` limit to the underlying space of the same limit formed in
`CompHaus`. -/
noncomputable def limitCompHausHomeomorph
    [∀ j, CompactSpace (F.obj j)] [∀ j, T2Space (F.obj j)] :
    ↥(limit F) ≃ₜ ↥(CompHaus.limitCone (compHausDiagram F)).pt :=
  TopCat.homeoOfIso
    (preservesLimitIso
        (forget₂ (TopModuleCat.{max u v} R) TopCat.{max u v}) F ≪≫
      (limit.isLimit _).conePointUniqueUpToIso
        (TopCat.limitConeIsLimit ((compHausDiagram F) ⋙ compHausToTop)))

/-- A limit of compact Hausdorff topological modules is compact. -/
theorem compactSpace_limit_of_compact_t2
    [∀ j, CompactSpace (F.obj j)] [∀ j, T2Space (F.obj j)] :
    CompactSpace ↥(limit F) :=
  (limitCompHausHomeomorph F).symm.compactSpace

/-- A limit of compact Hausdorff topological modules is Hausdorff. -/
theorem t2Space_limit_of_compact_t2
    [∀ j, CompactSpace (F.obj j)] [∀ j, T2Space (F.obj j)] :
    T2Space ↥(limit F) :=
  (limitCompHausHomeomorph F).symm.t2Space

end TopModuleCat
