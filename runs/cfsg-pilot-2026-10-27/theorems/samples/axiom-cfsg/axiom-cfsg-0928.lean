public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open Subgroup

section Subnormal

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem map_pPrimeCore_le_of_isSubnormal' [Fact p.Prime] {H : Subgroup G}
    (hH : H.IsSubnormal) : (CFSG.pPrimeCore p H).map H.subtype ≤ CFSG.pPrimeCore p G := by
  induction hH with
  | top => exact (CFSG.pPrimeCore_map_iso p (Subgroup.topEquiv (G := G))).le
  | step H K hle hK hN ih => exact (map_pPrimeCore_le_of_normal' hle hN).trans ih

end Subnormal
end CFSG.RankThree.PartTwo.Sec21.FF84
end
