public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim78

open CFSG.RankThree.GF2n (conjSubgroup_mul conjSubgroup_eq_self_iff card_conjSubgroup
  exists_mul_of_mem_sup le_normalizer_of_comm mem_normalizer_sup)

open CFSG.RankThree.PartTwo (omegaOneSub omegaOneSub_le)

variable {G : Type} [Group G]

variable [Finite G] {M B : Subgroup G}

theorem cover_of_five {L : Subgroup G} (hL : Nat.card ↥L = 16) {T : Finset (Subgroup G)}
    (hT : T.card = 5) (hle : ∀ Q ∈ T, Q ≤ L) (hcard : ∀ Q ∈ T, Nat.card ↥Q = 4)
    (hti : ∀ Q ∈ T, ∀ Q' ∈ T, Q ≠ Q' → Q ⊓ Q' = ⊥) :
    ∀ l ∈ L, l ≠ 1 → ∃ Q ∈ T, l ∈ Q := by
  classical
  have : Fintype G := Fintype.ofFinite G
  let S : Subgroup G → Finset G := fun Q => (Finset.univ.filter (· ∈ Q)).erase 1
  have hSc : ∀ Q : Subgroup G, Nat.card ↥Q = (Finset.univ.filter (· ∈ Q)).card := by
    intro Q
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h1mem : ∀ Q : Subgroup G, (1 : G) ∈ Finset.univ.filter (· ∈ Q) := fun Q => by
    simp
  have hS : ∀ Q : Subgroup G, (S Q).card = Nat.card ↥Q - 1 := by
    intro Q
    simp only [S]
    rw [Finset.card_erase_of_mem (h1mem Q), hSc]
  have hmemS : ∀ (Q : Subgroup G) (x : G), x ∈ S Q ↔ x ≠ 1 ∧ x ∈ Q := by
    intro Q x
    simp [S]
  have hdisj : ∀ Q ∈ T, ∀ Q' ∈ T, Q ≠ Q' → Disjoint (S Q) (S Q') := by
    intro Q hQ Q' hQ' hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [hmemS] at hx hx'
    have : x ∈ Q ⊓ Q' := ⟨hx.2, hx'.2⟩
    rw [hti Q hQ Q' hQ' hne, Subgroup.mem_bot] at this
    exact hx.1 this
  have hU : (T.biUnion S).card = 15 := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl (fun Q hQ => by rw [hS, hcard Q hQ])]
    simp [hT]
  intro l hl hl1
  by_contra hcon
  push Not at hcon
  have hl' : l ∉ T.biUnion S := by
    intro hmem
    rw [Finset.mem_biUnion] at hmem
    obtain ⟨Q, hQ, hx⟩ := hmem
    rw [hmemS] at hx
    exact hcon Q hQ hx.2
  have hsub : insert l (T.biUnion S) ⊆ S L := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · rw [hmemS]
      exact ⟨hl1, hl⟩
    · rw [Finset.mem_biUnion] at hx
      obtain ⟨Q, hQ, hx⟩ := hx
      rw [hmemS] at hx ⊢
      exact ⟨hx.1, hle Q hQ hx.2⟩
  have h16 : (insert l (T.biUnion S)).card = 16 := by
    rw [Finset.card_insert_of_notMem hl', hU]
  have h1 := Finset.card_le_card hsub
  rw [h16, hS, hL] at h1
  omega

end CFSG.CGT.PushingUpLit.SolKR2
end
