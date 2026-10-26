/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CompactNegativeDeflation
public import ContinuousGroupCohomology.FiniteTateDiagrams

/-!
# Compact negative Tate deflation diagrams

This file packages the compact Hausdorff finite Tate stages below
degree `-1`, and their continuous deflation maps, as diagrams over the open
normal subgroups of a profinite group. After forgetting topology and scalar
structure, the finite-bar comparisons assemble into natural
isomorphisms with the algebraic finite negative-deflation diagrams.

The compact parameter `n` represents Tate degree `-(n + 2)`, so its algebraic
counterpart is the homological diagram in degree `n + 1`. No topology on the
coefficient ring is used. In particular, these compact stage topologies are not
identified with those from `TopModuleCat.withModuleTopology`, and no inverse
limit or exactness statement is made here.

## References

The stage comparisons are those of `CompactNegativeTate`, using mathlib's
Tate-to-homology comparison by Yunzhou Xie and Yaël Dillies. The arrows use
`CompactNegativeDeflation` and mathlib's group-homology functoriality by
Amelia Livingston.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}
variable (A : Rep.{u} R G) (L : LevelCompact A)

/-- The compact Hausdorff finite negative-deflation diagram in Tate degree
`-(n + 2)`. -/
noncomputable def compactFiniteNegativeDeflationDiagram (n : ℕ) :
    OpenNormalSubgroup G ⥤ CompHausAddCommGrp.{u} where
  obj S := finiteTateNegative A L S n
  map {S T} f := by
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact finiteTateNegativeDeflation A L S T (leOfHom f) n
  map_id S := by
    let _ : Fintype (S.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact finiteTateNegativeDeflation_refl A L S n
  map_comp {S T U} f g := by
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    let _ : Fintype (U.toSubgroup.map (QuotientGroup.mk' T.toSubgroup)) :=
      Fintype.ofFinite _
    let _ : Fintype (U.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact
      (finiteTateNegativeDeflation_comp A L S T U (leOfHom f) (leOfHom g) n).symm

/-- The object of the compact negative-deflation diagram at an open normal
subgroup is its finite Tate stage. -/
@[simp]
lemma compactFiniteNegativeDeflationDiagram_obj (n : ℕ)
    (S : OpenNormalSubgroup G) :
    (compactFiniteNegativeDeflationDiagram A L n).obj S =
      finiteTateNegative A L S n := rfl

/-- An arrow of the compact negative-deflation diagram is the continuous
finite Tate deflation induced by the subgroup inclusion. -/
@[simp]
lemma compactFiniteNegativeDeflationDiagram_map (n : ℕ)
    {S T : OpenNormalSubgroup G} (f : S ⟶ T) :
    (compactFiniteNegativeDeflationDiagram A L n).map f =
      @finiteTateNegativeDeflation R G _ _ _ _ _ A L S T (leOfHom f)
        (Fintype.ofFinite _) n := rfl

/-- After forgetting scalar structure and compact topology, the algebraic
finite negative-deflation diagram in homological degree `n + 1` is naturally
isomorphic to the compact diagram in Tate degree `-(n + 2)`. -/
noncomputable def finiteNegativeDeflationAdditiveDiagramIso (n : ℕ) :
    finiteNegativeDeflationDiagram A (n + 1) ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
      compactFiniteNegativeDeflationDiagram A L n ⋙
        forget₂ CompHausAddCommGrp.{u} AddCommGrpCat.{u} :=
  NatIso.ofComponents
    (fun S ↦ (groupHomologyAddEquivFiniteTateNegative A L S n).toAddCommGrpIso)
    (fun {S T} f ↦ by
      let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
        Fintype.ofFinite _
      ext x
      exact
        groupHomologyAddEquivFiniteTateNegative_finiteNegativeDeflation
          A L S T (leOfHom f) n x)

/-- The component of the additive diagram comparison is the named finite-level
homology-to-compact equivalence. -/
@[simp]
lemma finiteNegativeDeflationAdditiveDiagramIso_app (n : ℕ)
    (S : OpenNormalSubgroup G) :
    (finiteNegativeDeflationAdditiveDiagramIso A L n).app S =
      (groupHomologyAddEquivFiniteTateNegative A L S n).toAddCommGrpIso := rfl

/-- Forward component evaluation is the finite-level additive comparison. -/
@[simp]
lemma finiteNegativeDeflationAdditiveDiagramIso_hom_app_apply (n : ℕ)
    (S : OpenNormalSubgroup G)
    (x : groupHomology (A.quotientToInvariants S.toSubgroup) (n + 1)) :
    (finiteNegativeDeflationAdditiveDiagramIso A L n).hom.app S x =
      groupHomologyAddEquivFiniteTateNegative A L S n x := rfl

/-- Inverse component evaluation is the inverse finite-level comparison. -/
@[simp]
lemma finiteNegativeDeflationAdditiveDiagramIso_inv_app_apply (n : ℕ)
    (S : OpenNormalSubgroup G) (x : finiteTateNegative A L S n) :
    (finiteNegativeDeflationAdditiveDiagramIso A L n).inv.app S x =
      (groupHomologyAddEquivFiniteTateNegative A L S n).symm x := rfl

end ContinuousGroupCohomology.LevelCompact
