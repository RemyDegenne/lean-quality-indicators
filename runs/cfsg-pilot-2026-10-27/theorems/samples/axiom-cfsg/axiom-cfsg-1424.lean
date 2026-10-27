public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22

open scoped IsMulCommutative

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

namespace FullIntertwinerHyp

variable {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {x : V}
  {η : C ≃ X₀}
  {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
    CFSG.Blueprint.NativeSporadic.M22}
  {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀} {α : setStab act lab Y C →* F₀}
  (H : FullIntertwinerHyp act lab Y C x η θ φ α)

variable {Φ : Y ≃ CFSG.Monster.B.Fischer.Y} (hΦ : IsCliqueIntertwiner act lab Y C x η φ α Φ)

include H hΦ

theorem exists_layer_three
    {w : W₀} (hw : w ∈ Lw 3) :
    ∃ r : Subgroup.closure (lab '' C), (r : S) ∈ labelLayer lab C 3 ∧ φ (Additive.ofMul r) = w := by
  set r : Subgroup.closure (lab '' C) := Additive.toMul (φ.symm w) with hr
  have hrw : φ (Additive.ofMul r) = w := by rw [hr, ofMul_toMul, LinearEquiv.apply_symm_apply]
  obtain ⟨i, hi, hri⟩ := H.slice.exists_mem_labelLayer H.clique (H.mem_ptStab r)
  refine ⟨r, ?_, hrw⟩
  interval_cases i
  · exfalso
    rw [labelLayer_zero, Set.mem_singleton_iff] at hri
    have hr1 : r = 1 := Subtype.ext hri
    rw [hr1, ofMul_one, map_zero] at hrw
    exact not_mem_Lw zero_mem_L0 (by norm_num : (0 : ℕ) ≠ 3) (hrw ▸ hw)
  · exfalso
    rw [H.slice.labelLayer_one H.clique] at hri
    obtain ⟨a, ha, hra⟩ := hri
    have hr1 : r = cliqueGen ⟨a, ha⟩ := Subtype.ext hra.symm
    rw [hr1, H.phi_cliqueGen] at hrw
    exact not_mem_Lw (coordImg_mem _) (by norm_num : (1 : ℕ) ≠ 3) (hrw ▸ hw)
  · exfalso
    have h2 : w ∈ Lw 2 := H.layer_two_eq hΦ ▸ ⟨r, hri, hrw⟩
    exact not_mem_Lw h2 (by norm_num : (2 : ℕ) ≠ 3) hw
  · exact hri

end FullIntertwinerHyp
end CFSG.Monster.B.TwoA.Fischer
end
