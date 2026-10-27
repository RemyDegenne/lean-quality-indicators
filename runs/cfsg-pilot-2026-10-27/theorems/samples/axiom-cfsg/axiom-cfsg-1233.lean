public section

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G]

variable [Finite G] {d₀ : B} {a z₀ : G}

theorem two_triangle_orbits
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    ∃ s₁ s₂ : Set G, IsTriangle a s₁ ∧ IsTriangle a s₂ ∧ (∀ g : G, conjSet g s₁ ≠ s₂) ∧
      ∀ s, IsTriangle a s → ∃ g : G, conjSet g s = s₁ ∨ conjSet g s = s₂ := by
  have ha : orderOf a = 2 := hG.1.1
  obtain ⟨y, hy⟩ := table7_nonempty I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG
    (IsConj.refl a) .two_A
  have hyA : IsConj a y := hy.1
  have hay : IsConj a (a * y) := hy.2
  have hlong := ncard_long_triangles I hG (IsConj.refl a) hyA hay
  have hne : (tableVIOrbit a z₀ a y .two_A).Nonempty := by
    rw [← Set.ncard_pos (Set.finite_of_ncard_pos (by
      rw [s341_ncard I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG (IsConj.refl a) hy
        .two_A]; norm_num [tableVISize]))]
    rw [s341_ncard I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG (IsConj.refl a) hy .two_A]
    norm_num [tableVISize]
  obtain ⟨γ, hγ⟩ := hne
  have hS := isShortTriangle_mul ha (IsConj.refl a) hyA hay
  have hL := isLongTriangle_of_mem_orbit ha (IsConj.refl a) hyA hay hγ
  refine ⟨{a, y, a * y}, {a, y, γ}, hS.1, hL.1, fun g e => hL.2 (e ▸ hS.conjSet g), ?_⟩
  intro s hs
  have hfin : s.Finite := Set.finite_of_ncard_pos (by rw [hs.1]; norm_num)
  obtain ⟨α, hα⟩ : s.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hs.1]; norm_num)
  obtain ⟨β, hβs, hβα⟩ : ∃ β ∈ s, β ≠ α := by
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    have : s ⊆ {α} := fun x hx => hc x hx
    have := Set.ncard_le_ncard this (Set.finite_singleton α)
    rw [hs.1, Set.ncard_singleton] at this
    exact absurd this (by norm_num)
  have hαA := hs.2.1 α hα
  have hβA := hs.2.1 β hβs
  have hαβ := hs.2.2 α hα β hβs (Ne.symm hβα)
  obtain ⟨g₁, hg₁⟩ := isConj_iff.1 hαA
  have hβ' : g₁⁻¹ * β * g₁ ∈ twoANbr a a := by
    refine ⟨hβA.trans (isConj_iff.2 ⟨g₁⁻¹, by group⟩), ?_⟩
    have e : a * (g₁⁻¹ * β * g₁) = g₁⁻¹ * (α * β) * g₁ := by rw [← hg₁]; group
    rw [e]
    exact hαβ.trans (isConj_iff.2 ⟨g₁⁻¹, by group⟩)
  obtain ⟨g₂, hg₂, hg₂β⟩ := table7_transitive I.sls I.tableV I.leech I.tableIII I.tableIVBaby
    I.threeSwap I.leechPair hG (IsConj.refl a) (K := .two_A) hβ' hy
  have hg₂a : g₂ * a * g₂⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hg₂, mul_inv_cancel_right]
  set g := g₂ * g₁⁻¹ with hg
  have hgα : g * α * g⁻¹ = a := by rw [hg, ← hg₁]; calc
    g₂ * g₁⁻¹ * (g₁ * a * g₁⁻¹) * (g₂ * g₁⁻¹)⁻¹ = g₂ * a * g₂⁻¹ := by group
    _ = a := hg₂a
  have hgβ : g * β * g⁻¹ = y := by
    rw [← hg₂β, hg]; group
  have hs' := hs.conjSet g
  have ha' : a ∈ conjSet g s := ⟨α, hα, hgα⟩
  have hy' : y ∈ conjSet g s := ⟨β, hβs, hgβ⟩
  have hya : a ≠ y := fun h => by
    rw [← h] at hay
    have := orderOf_eq_of_isConj hay
    rw [ha, orderOf_eq_one_iff.2 (mul_self_of_isConj ha (IsConj.refl a))] at this
    exact absurd this (by norm_num)
  obtain ⟨γ', hγ's, hγ'a, hγ'y, he⟩ := eq_insert_of_isTriangle hs' ha' hy' hya
  by_cases hshort : IsShortTriangle a (conjSet g s)
  · refine ⟨g, Or.inl ?_⟩
    rw [he]
    have hab := hshort.2 a ha' y hy' hya
    rw [he] at hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hab
    rcases hab with h | h | h
    · exact absurd (mul_left_cancel (h.trans (mul_one a).symm)) (fun e => by
        rw [e] at hyA
        have := orderOf_eq_of_isConj hyA
        rw [ha, orderOf_one] at this
        exact absurd this (by norm_num))
    · exact absurd (mul_right_cancel (h.trans (one_mul y).symm)) (fun e => by
        have := ha
        rw [e, orderOf_one] at this
        exact absurd this (by norm_num))
    · rw [h]
  ·
    have hγ'O : γ' ∈ tableVIOrbit a z₀ a y .two_A := by
      have hγ'A := hs'.2.1 γ' hγ's
      refine ⟨⟨⟨hγ'A, hs'.2.2 y hy' γ' hγ's (Ne.symm hγ'y)⟩, hγ'a, ?_⟩,
        hs'.2.2 a ha' γ' hγ's (Ne.symm hγ'a)⟩
      intro e
      apply hshort
      rw [he, e]
      exact isShortTriangle_mul ha (IsConj.refl a) hyA hay
    obtain ⟨g₃, hg₃, hg₃γ⟩ := s341_transitive I.sls I.tableV I.leech I.tableIII I.tableIVBaby
      I.threeSwap I.leechPair hG (IsConj.refl a) hy hγ'O hγ
    obtain ⟨hg₃a, hg₃y⟩ := Subgroup.mem_inf.1 hg₃
    refine ⟨g₃ * g, Or.inr ?_⟩
    rw [← conjSet_conjSet, he, conjSet_insert, conjSet_insert, conjSet_singleton,
      Subgroup.mem_centralizer_singleton_iff.1 hg₃a, mul_inv_cancel_right,
      Subgroup.mem_centralizer_singleton_iff.1 hg₃y, mul_inv_cancel_right, hg₃γ]

end CFSG.Monster.Existence
end
