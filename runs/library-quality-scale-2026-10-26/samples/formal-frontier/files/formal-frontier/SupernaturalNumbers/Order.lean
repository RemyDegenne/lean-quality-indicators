/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SupernaturalNumbers.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

/-!
# Supernatural orders and indices

This file gives the finite-quotient definitions of the supernatural order of a
profinite group and the supernatural index of a closed subgroup.  It also gives
the corresponding finite-subgroup definition for an abelian torsion group.
-/

@[expose] public section

namespace Supernatural

/-- The supernatural number associated to the cardinality of a finite nonempty type. -/
noncomputable def ofFiniteCard (X : Type*) [Finite X] [Nonempty X] : Supernatural :=
  ofPNat ⟨Nat.card X, Nat.card_pos⟩

/-- The supernatural number associated to a finite subgroup index. -/
noncomputable def ofFiniteIndex {G : Type*} [Group G] (H : Subgroup G)
    [H.FiniteIndex] : Supernatural :=
  ofPNat ⟨H.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero⟩

/-- The supernatural order of a profinite group, obtained from all finite quotients. -/
noncomputable def profiniteOrder (G : ProfiniteGrp) : Supernatural :=
  ⨆ U : OpenNormalSubgroup G, ofFiniteCard (G ⧸ U.toSubgroup)

/-- Every finite quotient order divides the supernatural order of the profinite group. -/
theorem quotientOrder_le_profiniteOrder (G : ProfiniteGrp) (U : OpenNormalSubgroup G) :
    ofFiniteCard (G ⧸ U.toSubgroup) ≤ profiniteOrder G :=
  le_iSup (fun V : OpenNormalSubgroup G ↦ ofFiniteCard (G ⧸ V.toSubgroup)) U

/-- The supernatural index of a closed subgroup of a profinite group. -/
noncomputable def profiniteIndex {G : ProfiniteGrp} (H : ClosedSubgroup G) : Supernatural :=
  ⨆ U : OpenNormalSubgroup G,
    ofFiniteIndex (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup))

/-- Every finite-quotient index divides the supernatural index. -/
theorem quotientIndex_le_profiniteIndex {G : ProfiniteGrp} (H : ClosedSubgroup G)
    (U : OpenNormalSubgroup G) :
    ofFiniteIndex (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)) ≤ profiniteIndex H :=
  le_iSup (fun V : OpenNormalSubgroup G ↦
    ofFiniteIndex (H.toSubgroup.map (QuotientGroup.mk' V.toSubgroup))) U

/-- The trivial subgroup as a closed subgroup of a profinite group. -/
def trivialClosedSubgroup (G : ProfiniteGrp) : ClosedSubgroup G where
  toSubgroup := ⊥
  isClosed' := isClosed_singleton

/-- The whole profinite group as a closed subgroup. -/
def wholeClosedSubgroup (G : ProfiniteGrp) : ClosedSubgroup G where
  toSubgroup := ⊤
  isClosed' := isClosed_univ

/-- The whole profinite group as an open normal subgroup. -/
def wholeOpenNormalSubgroup (G : ProfiniteGrp) : OpenNormalSubgroup G where
  toOpenSubgroup := {
    toSubgroup := ⊤
    isOpen' := isOpen_univ
  }
  isNormal' := Subgroup.normal_top

/-- The index of the trivial closed subgroup is the order of the profinite group. -/
theorem profiniteIndex_trivial (G : ProfiniteGrp) :
    profiniteIndex (trivialClosedSubgroup G) = profiniteOrder G := by
  simp [profiniteIndex, profiniteOrder, ofFiniteIndex, ofFiniteCard, trivialClosedSubgroup]

/-- The whole profinite group has supernatural index one. -/
theorem profiniteIndex_whole (G : ProfiniteGrp) :
    profiniteIndex (wholeClosedSubgroup G) = 1 := by
  apply le_antisymm
  · refine iSup_le fun U ↦ ?_
    simp only [ofFiniteIndex, wholeClosedSubgroup, Subgroup.map_top,
      QuotientGroup.range_mk', Subgroup.index_top, PNat.mk_ofNat, ofPNat_one]
    exact le_rfl
  · refine le_iSup_of_le (wholeOpenNormalSubgroup G) ?_
    simp only [ofFiniteIndex, wholeClosedSubgroup, Subgroup.map_top,
      QuotientGroup.range_mk', Subgroup.index_top, PNat.mk_ofNat, ofPNat_one]
    exact le_rfl

/-- Supernatural index reverses inclusion of closed subgroups. -/
theorem profiniteIndex_antitone {G : ProfiniteGrp} {H K : ClosedSubgroup G}
    (h : H ≤ K) : profiniteIndex K ≤ profiniteIndex H := by
  refine iSup_le fun U ↦ le_iSup_of_le U ?_
  apply ofPNat_le_ofPNat_iff.mpr
  exact PNat.dvd_iff.mpr (Subgroup.index_dvd_of_le (Subgroup.map_mono h))

/-- Additive subgroups carrying a proof that their underlying type is finite. -/
def FiniteAddSubgroup (A : Type*) [AddGroup A] :=
  {B : AddSubgroup A // Finite B}

/-- The supernatural order of an abelian torsion group, obtained from its finite subgroups. -/
noncomputable def torsionOrder (A : Type*) [AddCommGroup A]
    (_hA : IsAddTorsion A) : Supernatural :=
  ⨆ B : FiniteAddSubgroup A,
    @ofFiniteCard B.1 B.2 (inferInstanceAs (Nonempty B.1))

/-- The order of every finite subgroup divides the supernatural torsion order. -/
theorem finiteAddSubgroupOrder_le_torsionOrder (A : Type*) [AddCommGroup A]
    (hA : IsAddTorsion A) (B : FiniteAddSubgroup A) :
    @ofFiniteCard B.1 B.2 (inferInstanceAs (Nonempty B.1)) ≤ torsionOrder A hA :=
  le_iSup (fun C : FiniteAddSubgroup A ↦
    @ofFiniteCard C.1 C.2 (inferInstanceAs (Nonempty C.1))) B

/-- For a finite abelian group, torsion order agrees with the ordinary cardinality. -/
theorem torsionOrder_eq_ofFiniteCard (A : Type*) [AddCommGroup A] [Finite A]
    (hA : IsAddTorsion A) : torsionOrder A hA = ofFiniteCard A := by
  apply le_antisymm
  · refine iSup_le fun B ↦ ?_
    apply ofPNat_le_ofPNat_iff.mpr
    exact PNat.dvd_iff.mpr B.1.card_addSubgroup_dvd_card
  · let B : FiniteAddSubgroup A := ⟨⊤, inferInstance⟩
    refine le_iSup_of_le B ?_
    simp only [ofFiniteCard, AddSubgroup.mem_top, Nat.card_subtype_true, B]
    exact le_rfl

end Supernatural
