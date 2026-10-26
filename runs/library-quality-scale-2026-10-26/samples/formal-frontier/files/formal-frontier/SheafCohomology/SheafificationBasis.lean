/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Sheafify

public section

set_option warningAsError true

/-!
# Detecting sheafified isomorphisms on a basis

An `AddCommGrpCat`-valued presheaf morphism that is an isomorphism on a basis
becomes an isomorphism after sheafification.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open TopCat TopologicalSpace

universe u

namespace SheafCohomology.HigherDirectImageFilteredColimit

variable {X : TopCat.{u}}
variable {B : Set (Opens X)} (hB : Opens.IsBasis B)
variable {F G : X.Presheaf AddCommGrpCat.{u}} {α : F ⟶ G}

include hB

theorem stalkFunctor_map_surjective_of_isBasis
    (hα : ∀ U ∈ B, Function.Surjective (α.app (op U))) (x : X) :
    Function.Surjective ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α) := by
  intro t
  obtain ⟨U, hxU, hU, s, rfl⟩ :=
    Presheaf.exists_mem_germ_eq_of_isBasis hB G x t
  obtain ⟨r, hr⟩ := hα U hU s
  refine ⟨F.germ U x hxU r, ?_⟩
  rw [Presheaf.stalkFunctor_map_germ_apply, hr]

theorem stalkFunctor_map_bijective_of_isBasis
    (hα : ∀ U ∈ B, Function.Bijective (α.app (op U))) (x : X) :
    Function.Bijective ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α) :=
  ⟨Presheaf.stalkFunctor_map_injective_of_isBasis hB
      (fun U hU => (hα U hU).injective) x,
    stalkFunctor_map_surjective_of_isBasis hB
      (fun U hU => (hα U hU).surjective) x⟩

/-- A morphism of `AddCommGrpCat`-valued presheaves that is an isomorphism on
a basis becomes an isomorphism after sheafification. -/
theorem presheafToSheaf_map_isIso_of_isBasis
    (hα : ∀ U ∈ B, IsIso (α.app (op U))) :
    IsIso ((presheafToSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).map α) := by
  let PF : X.Sheaf AddCommGrpCat.{u} :=
    (presheafToSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj F
  let PG : X.Sheaf AddCommGrpCat.{u} :=
    (presheafToSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj G
  let φ : PF ⟶ PG :=
    (presheafToSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).map α
  change IsIso φ
  rw [Presheaf.isIso_iff_stalkFunctor_map_iso]
  intro x
  let J := Opens.grothendieckTopology X
  let S := Presheaf.stalkFunctor AddCommGrpCat.{u} x
  change IsIso (S.map (sheafifyMap J α))
  have hα_bij : ∀ U ∈ B, Function.Bijective (α.app (op U)) := by
    intro U hU
    let _ : IsIso (α.app (op U)) := hα U hU
    exact ConcreteCategory.bijective_of_isIso (α.app (op U))
  let _ : IsIso (S.map α) :=
    (ConcreteCategory.isIso_iff_bijective (S.map α)).2
      (stalkFunctor_map_bijective_of_isBasis hB hα_bij x)
  let _ : IsIso (S.map (toSheafify J F)) :=
    Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} F
  let _ : IsIso (S.map (toSheafify J G)) :=
    Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} G
  let _ : IsIso (S.map α ≫ S.map (toSheafify J G)) := inferInstance
  have heq :
      S.map α ≫ S.map (toSheafify J G) =
        S.map (toSheafify J F) ≫ S.map (sheafifyMap J α) := by
    rw [← S.map_comp, ← S.map_comp, toSheafify_naturality]
  exact IsIso.of_isIso_fac_left heq.symm

#print axioms stalkFunctor_map_surjective_of_isBasis
#print axioms stalkFunctor_map_bijective_of_isBasis
#print axioms presheafToSheaf_map_isIso_of_isBasis

end SheafCohomology.HigherDirectImageFilteredColimit
