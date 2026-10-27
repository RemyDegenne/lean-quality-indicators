public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG.Open Finset

open CFSG.HardMathSupport.Solomon.Coordinator (lieOrderBridge_holds)

open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula add_one_dvd_sq_sub_one)

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (IsTwoPow IsL2EightIndex)

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux (IsSmallTwistedIdx)

open CFSG.HardMathSupport.Dickson.Bal207 (SpCompType SpCompIdx ExcU62Type ExcU62CompIdx
  OrthCompType OrthCompIdx G28CompType)

section Orders

theorem two_pow_dvd_pow_of_even {q : ℕ} (hq : Even q) (N : ℕ) : 2 ^ N ∣ q ^ N :=
  pow_dvd_pow_of_dvd (even_iff_two_dvd.mp hq) N

end Orders
end CFSG.RankThree.PartTwo.Sec4.Ronan148R
end
