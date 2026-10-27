public section

namespace CFSG.CGT.Foote81L6

open DihedralGroup

section E4

theorem e4_card {b : ℕ} (hb : b = 1) : Nat.card (DihedralGroup (2 ^ b)) = 4 := by
  subst hb; simp [DihedralGroup.nat_card]

end E4
end CFSG.CGT.Foote81L6
end
