public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringK419.ReeF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.LargeReeInvolution

theorem three_dvd_sq_sub_one (a : ℕ) : 3 ∣ (2 ^ (2 * a + 1)) ^ 2 - 1 := by
  have h : (2 ^ (2 * a + 1)) ^ 2 = 4 ^ (2 * a + 1) := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h]
  simpa using Nat.sub_dvd_pow_sub_pow 4 1 (2 * a + 1)

end CFSG.RankThree.PartTwo.Sec4.HeringK419.ReeF4
end
