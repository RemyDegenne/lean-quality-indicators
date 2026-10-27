public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

theorem sp4_mul_three_ne_U3 {m p e : ℕ} (hm : 2 ≤ m) (hp : p.Prime) (hp3 : p ≠ 3) (he : 1 ≤ e) :
    (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) * 3 ≠
      (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) := by
  intro hEq
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exact sp4Arith_two_U3 hm he hEq
  · obtain ⟨hQodd, hQ5, hQ3⟩ := sp4Arith_odd_prime_pow hp hodd hp3 he
    have key : (p ^ e) ^ 3 * ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1) =
        3 * (2 ^ (m * 4) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1))) := by
      rw [pow_mul]
      calc (p ^ e) ^ 3 * ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)
          = (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) := by ring
        _ = (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) * 3 := hEq.symm
        _ = 3 * ((2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1))) := by ring
    exact CFSG.RankThree.PartTwo.Sec19.Step1917Steps.false_of_sl3Order_eq_sp4
      hQodd hQ5 hQ3 (by omega) (Or.inr key)

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
end
