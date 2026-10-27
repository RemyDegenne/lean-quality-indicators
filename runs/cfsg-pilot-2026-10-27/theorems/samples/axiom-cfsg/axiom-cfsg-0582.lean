public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

theorem eq_bot_of_normalTwoComplement {Y : Type} [Group Y] [Finite Y] (Gs : Subgroup Y)
    [Gs.Normal] (hO2 : ∀ P : Subgroup Y, P.Normal → IsPGroup 2 P → P = ⊥)
    (hO : ∀ P : Subgroup Y, P.Normal → Odd (Nat.card P) → P = ⊥) (X : Subgroup ↥Gs)
    [X.Normal] (h : HasNormalTwoComplement ↥X) : X = ⊥ := by
  obtain ⟨O, hOn, hOodd, hOn', hOq⟩ := h
  obtain ⟨M, hM⟩ : ∃ M : Subgroup ↥Gs, M = O.map X.subtype := ⟨_, rfl⟩
  have hMX : M ≤ X := by
    rw [hM]
    intro m hm
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hm
    exact x.2
  have hMcard : Odd (Nat.card M) := by
    rw [hM, Subgroup.card_map_of_injective X.subtype_injective]
    exact hOodd
  have hconjX : ∀ g : ↥Gs, conjSubgroup g M ≤ X := by
    intro g y hy
    have h1 := Subgroup.Normal.conj_mem ‹X.Normal› _ (hMX (mem_conjSubgroup.mp hy)) g
    rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h1
  have hconj : ∀ g : ↥Gs, conjSubgroup g M ≤ M := by
    intro g y hy
    have hyX : y ∈ X := hconjX g hy
    have hcardconj : Nat.card ↥(conjSubgroup g M) = Nat.card ↥M :=
      Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (K := M)
        (MulAut.conj g).injective
    have hN : Odd (Nat.card ↥((conjSubgroup g M).subgroupOf X)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hconjX g)).toEquiv, hcardconj]
      exact hMcard
    have hsub := normalTwoComplement_odd_le O hOq _ hN
    have hmem : (⟨y, hyX⟩ : ↥X) ∈ O := hsub (Subgroup.mem_subgroupOf.mpr hy)
    rw [hM]
    exact Subgroup.mem_map.mpr ⟨⟨y, hyX⟩, hmem, rfl⟩
  have hMn : M.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : g * n * g⁻¹ ∈ conjSubgroup g M := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * n * g⁻¹) * g = n by group]
      exact hn
    exact hconj g h1
  have hM0 : M = ⊥ := by
    have hpc : CFSG.pPrimeCore 2 ↥Gs = ⊥ := corB_pPrimeCore_sub_eq_bot hO Gs
    exact CFSG.pPrimeCore_eq_bot_iff.mp hpc M hMn (Nat.coprime_two_left.mpr hMcard)
  have hO0 : O = ⊥ := by
    have hmap : O.map X.subtype = ⊥ := by
      rw [← hM]
      exact hM0
    exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hmap
  have hXp : IsPGroup 2 ↥X := by
    intro x
    obtain ⟨k, hk⟩ := hOq (x : ↥X ⧸ O)
    refine ⟨k, ?_⟩
    have h1 : ((x ^ 2 ^ k : ↥X) : ↥X ⧸ O) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hk
    have h2 : x ^ 2 ^ k ∈ O := (QuotientGroup.eq_one_iff _).mp h1
    rw [hO0, Subgroup.mem_bot] at h2
    exact h2
  have hXle : X ≤ CFSG.pCore 2 ↥Gs :=
    le_sSup (show X ∈ {K : Subgroup ↥Gs | K.Normal ∧ IsPGroup 2 K} from ⟨inferInstance, hXp⟩)
  rw [corB_pCore_sub_eq_bot hO2 Gs, le_bot_iff] at hXle
  exact hXle

end CFSG.RankThree.GF2n.Stroth80
end
