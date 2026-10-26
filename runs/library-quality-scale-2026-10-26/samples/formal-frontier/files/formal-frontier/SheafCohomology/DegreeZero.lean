/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import SheafCohomology.CompactOpenSections

public section

/-!
# Degree-zero sheaf cohomology

This file identifies degree-zero sheaf cohomology with sections on the
terminal open.  It then transports the compact-global-sections filtered
colimit theorem across that natural isomorphism.

The choice of `HasExt` is explicit: mathlib deliberately does not install a
global instance because the universe of Ext groups is part of the API.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace

universe u v

namespace SheafCohomology.DegreeZero

variable {X : Type u} [TopologicalSpace X]

variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
variable [HasExt.{v} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{v})]

/-- Degree-zero sheaf cohomology is naturally isomorphic to sections on the
terminal open. -/
@[expose] def functorHZeroIsoSections :
    CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) 0 ≅
      CompactOpenSections.sections (⊤ : Opens X) :=
  NatIso.ofComponents
    (fun F => (CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop).toAddCommGrpIso)
    (by
      intro F G f
      ext x
      exact (CategoryTheory.Sheaf.H.equiv₀_naturality
        isTerminalTop f x).symm)

variable [UnivLE.{u, v}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective
  AddCommGrpCat.{v}]
variable {I : Type v} [SmallCategory I] [IsFiltered I]
variable (F : I ⥤ CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{v})

/-- On a compact prespectral quasi-separated space, degree-zero sheaf
cohomology preserves same-size filtered colimits. -/
theorem preservesColimit_functorH_zero
    [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X] :
    PreservesColimit F (CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology X) 0) := by
  exact (preservesColimit_iff_of_natIso F
    (functorHZeroIsoSections (X := X))).mpr
      (CompactOpenSections.preservesColimit_globalSections F)

end SheafCohomology.DegreeZero
