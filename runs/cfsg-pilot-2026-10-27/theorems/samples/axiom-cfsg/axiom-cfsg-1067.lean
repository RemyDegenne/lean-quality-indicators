public section

namespace CFSG.Quasithin

namespace SL2Sylow

open scoped MatrixGroups

open Matrix Matrix.SpecialLinearGroup

variable {F : Type*} [Field F]

theorem exists_ne_zero_sq_ne_one [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fintype F := Fintype.ofFinite F
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have h1 : a ^ 2 = 1 := hcon a ha
      have h2 : (a - 1) ^ 2 = 0 := by
        linear_combination h1 + (1 - a) * (CharTwo.two_eq_zero (R := F))
      have h3 : a = 1 := sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)
      simp [h3]
  have := Finset.card_le_card hsub
  have h2 : (({0, 1} : Finset F)).card ≤ 2 := Finset.card_le_two
  rw [Nat.card_eq_fintype_card] at hq
  simp only [Finset.card_univ] at this
  omega

end SL2Sylow
end CFSG.Quasithin
end
