public section

namespace CFSG.Quasithin

namespace H

namespace L3Wr

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix CFSG.Quasithin.H13

open scoped Matrix

theorem card_fixV_rho_le_of_seven {a b : ↥SL32} (ha : a ^ 7 = 1) (hb : b ^ 7 = 1)
    (hab : (a, b) ≠ 1) : Nat.card ↥(fixV (Subgroup.zpowers (rho (a, b)))) ≤ 32 := by
  have h1 : ∀ r : ↥SL32, (r = slOfMat s7m det_s7m ∨ r = slOfMat s7i det_s7i) →
      Nat.card ↥(fixV (Subgroup.zpowers (rho (r, 1)))) ≤ 32 := by
    rintro r (rfl | rfl)
    · rw [card_fixV_rho]
      exact card_filter_s7m_one.le.trans (by norm_num)
    · rw [card_fixV_rho]
      exact card_filter_s7i_one.le.trans (by norm_num)
  by_cases ha1 : a = 1
  · subst ha1
    have hb1 : b ≠ 1 := fun h => hab (by rw [h]; rfl)
    obtain ⟨g, hg | hg⟩ := exists_eq_conj_s7m hb hb1 <;> rw [hg, card_fixV_rho_swap,
      card_fixV_rho_conj_left]
    · exact h1 _ (Or.inl rfl)
    · exact h1 _ (Or.inr rfl)
  · obtain ⟨g, hg | hg⟩ := exists_eq_conj_s7m ha ha1
    · rw [hg]
      by_cases hb1 : b = 1
      · subst hb1
        rw [card_fixV_rho_conj_left]
        exact h1 _ (Or.inl rfl)
      · obtain ⟨h, hh | hh⟩ := exists_eq_conj_s7m hb hb1 <;> rw [hh, card_fixV_rho_conj,
          card_fixV_rho]
        · exact card_filter_s7m_s7m.trans (by norm_num)
        · exact card_filter_s7m_s7i.trans (by norm_num)
    · rw [hg]
      by_cases hb1 : b = 1
      · subst hb1
        rw [card_fixV_rho_conj_left]
        exact h1 _ (Or.inr rfl)
      · obtain ⟨h, hh | hh⟩ := exists_eq_conj_s7m hb hb1 <;> rw [hh, card_fixV_rho_conj,
          card_fixV_rho]
        · exact card_filter_s7i_s7m.trans (by norm_num)
        · exact card_filter_s7i_s7i.trans (by norm_num)

end L3Wr
end H
end CFSG.Quasithin
end
