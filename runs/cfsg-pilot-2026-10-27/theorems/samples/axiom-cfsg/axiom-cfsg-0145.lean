public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.B1 CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Offender CFSG.SL2MinimalFaithful
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6

open scoped commutatorElement

section Ambient

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E : Subgroup Γ}

theorem block_structure_three_fixed (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    (hn : IsNaturalAltModule ↥E 1) :
    (blockW E ⊓ Subgroup.centralizer (baum T : Set Γ)).relIndex (blockW E) = 2 ∧
      ∀ b ∈ baum T, b ∉ Subgroup.centralizer (blockW E : Set Γ) →
        blockW E ⊓ Subgroup.centralizer ({b} : Set Γ) =
          blockW E ⊓ Subgroup.centralizer (baum T : Set Γ) := by
  classical
  have hWE : blockW E = pCoreOf 2 E := blockW_eq_pCoreOf hE
  have h6 := six_four_d hG hT hE
  rw [hWE] at h6 ⊢
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  have hWe : IsElemAbelian 2 W := isElemAbelian_of_forall' hE.elemAbelian.1 hE.elemAbelian.2
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWe
  have hcard4 : Nat.card ↥W = 4 := by
    obtain ⟨D, -, -, hβbij, -⟩ := block_structure_three hG hT hE hn hWdef hWe
    rw [Nat.card_congr (Equiv.ofBijective D.β hβbij)]
    exact card_coreMod_three'
  have hWT : W ≤ T := pCoreOf_le_sylow hG hT hE hT
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hW2 : IsPGroup 2 ↥W := hT2.to_le hWT
  have hB2 : IsPGroup 2 ↥(baum T) := hT2.to_le (inf_le_left : baum T ≤ T)
  have hBN : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hBW : baum T ≤ Subgroup.normalizer (W : Set Γ) :=
    hBN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hWne : W ≠ ⊥ := pCoreOf_ne_bot hE (charTwo_of_isBTBlock hG hT hE)
  have hBnc : ¬ baum T ≤ Subgroup.centralizer (W : Set Γ) := by
    intro hle
    apply h6
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro w hw j hj
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hle (B6.thompsonJ_le_baum T hj)) w hw
  obtain ⟨w₀, hw₀W, hw₀1, hw₀fix⟩ := exists_ne_one_fixed_of_isPGroup hW2 hWne hB2 hBW
  have hw₀C : w₀ ∈ Subgroup.centralizer (baum T : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have := hw₀fix p hp
    calc p * w₀ = (p * w₀ * p⁻¹) * p := by group
      _ = w₀ * p := by rw [this]
  have hX : (Subgroup.centralizer (baum T : Set Γ)).relIndex W *
      Nat.card ↥(Subgroup.centralizer (baum T : Set Γ) ⊓ W) = 4 := by
    rw [Subgroup.relIndex_mul_card, hcard4]
  have hr1 : (Subgroup.centralizer (baum T : Set Γ)).relIndex W ≠ 1 := by
    intro h
    have hle : W ≤ Subgroup.centralizer (baum T : Set Γ) := Subgroup.relIndex_eq_one.mp h
    apply hBnc
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hle hw) b hb).symm
  have hc1 : Nat.card ↥(Subgroup.centralizer (baum T : Set Γ) ⊓ W) ≠ 1 := by
    intro h
    rw [Subgroup.card_eq_one] at h
    apply hw₀1
    have : w₀ ∈ Subgroup.centralizer (baum T : Set Γ) ⊓ W := ⟨hw₀C, hw₀W⟩
    rw [h] at this
    exact Subgroup.mem_bot.mp this
  have hr2 : (Subgroup.centralizer (baum T : Set Γ)).relIndex W = 2 ∧
      Nat.card ↥(Subgroup.centralizer (baum T : Set Γ) ⊓ W) = 2 := by
    have hr4 : (Subgroup.centralizer (baum T : Set Γ)).relIndex W ≤ 4 :=
      Nat.le_of_dvd (by norm_num) ⟨_, hX.symm⟩
    generalize (Subgroup.centralizer (baum T : Set Γ)).relIndex W = r at hX hr1 hr4 ⊢
    generalize Nat.card ↥(Subgroup.centralizer (baum T : Set Γ) ⊓ W) = c at hX hc1 ⊢
    interval_cases r <;> omega
  refine ⟨?_, ?_⟩
  · rw [Subgroup.inf_relIndex_left]
    exact hr2.1
  · intro b hb hbN
    have hXY : W ⊓ Subgroup.centralizer (baum T : Set Γ) ≤ W ⊓ Subgroup.centralizer ({b} : Set Γ) :=
      inf_le_inf_left W (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
    refine (Subgroup.eq_of_le_of_card_ge hXY ?_).symm
    have hs : (Subgroup.centralizer ({b} : Set Γ)).relIndex W *
        Nat.card ↥(Subgroup.centralizer ({b} : Set Γ) ⊓ W) = 4 := by
      rw [Subgroup.relIndex_mul_card, hcard4]
    have hs1 : (Subgroup.centralizer ({b} : Set Γ)).relIndex W ≠ 1 := by
      intro h
      have hle : W ≤ Subgroup.centralizer ({b} : Set Γ) := Subgroup.relIndex_eq_one.mp h
      apply hbN
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (Subgroup.mem_centralizer_iff.mp (hle hw) b (Set.mem_singleton b)).symm
    have hYle : Nat.card ↥(Subgroup.centralizer ({b} : Set Γ) ⊓ W) ≤ 2 := by
      generalize (Subgroup.centralizer ({b} : Set Γ)).relIndex W = s at hs hs1
      generalize Nat.card ↥(Subgroup.centralizer ({b} : Set Γ) ⊓ W) = c at hs
      have : s ≤ 4 := Nat.le_of_dvd (by norm_num) ⟨_, hs.symm⟩
      interval_cases s <;> omega
    have hXcard : Nat.card ↥(W ⊓ Subgroup.centralizer (baum T : Set Γ)) = 2 := by
      rw [inf_comm]; exact hr2.2
    have hYc : Nat.card ↥(W ⊓ Subgroup.centralizer ({b} : Set Γ)) ≤ 2 := by
      rw [inf_comm]; exact hYle
    omega

end Ambient
end CFSG.CGT.PushingUpLit.BHS7
end
