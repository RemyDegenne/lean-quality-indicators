public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open Matrix CFSG.RankThree.Classical

open scoped MatrixGroups

variable {K : Type} [Field K]

section Pairing

variable {E : Type*} [Group E] {π : E →* SL(4, K)} (hπ : Function.Surjective π)
  (hZ : π.ker ≤ Subgroup.center E)

variable (c : Kˣ)

theorem wt_tor2_1 : wtR (tor2 c) 1 = (c : K) ^ 2 := by
  simp [wtR, tor2]
  ring

end Pairing
end CFSG.ClassicalInvolution.Asc77.SCH
end
