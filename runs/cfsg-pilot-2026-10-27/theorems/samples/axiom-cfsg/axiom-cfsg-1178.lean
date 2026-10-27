public section

namespace CFSG.Quasithin.H13.NQCat.NGT

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

local notation "StSL" => CFSG.Assembly.LowTwoRank.StatedSL

local notation "StSp" => CFSG.Assembly.LowTwoRank.StatedSp

section Excl

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U Z : Subgroup V} {n : ℕ}

theorem excl_g2 (hn : 2 ≤ n) (hL : Nat.card L = sl3Form n ∨ Nat.card L = sp4Form n) {a : ℕ}
    (h : G2Natural L U Z a) : False := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have ha := one_le_of_card_field hK
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      ha hK
  have hcard : Nat.card L = Nat.card ↥(CFSG.Open.quasithinG2 K) :=
    card_eq_of_realizesVia (FFC.zornQ_faithful _ le_rfl) hπ
  rw [card_g2_form hK] at hcard
  rcases hL with h | h
  · exact sl3Form_ne_g2Form ha (by omega) (h.symm.trans hcard)
  · exact sp4Form_ne_g2Form ha (by omega) (h.symm.trans hcard)

end Excl
end CFSG.Quasithin.H13.NQCat.NGT
end
