public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.YGroups

open CFSG.Sporadic.Bridge (wordProd)

open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels powWord)

open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

theorem y433_pair
    {s t : ℕ} (hs : s < 11) (ht : t < 11) (hst : s < t) :
    (y433Img s * y433Img t) ^ pairExp 4 3 3 s t = 1 := by
  by_cases ht10 : t = 10
  · subst ht10
    have hs10 : s < 10 := by omega
    rw [y433Img_ten, y433Img_of_lt hs10, y433_pairExp_ten s hs10]
    by_cases hs9 : s = 9
    · subst hs9
      rw [ite_eq_left rfl, y433_sigma_nine]
      exact fiE_eight_mul_gammaZero_pow_three
    · rw [ite_eq_right hs9]
      exact y433M_sq_of_commute (y433M_fiE_mul_self (y433Sigma_lt hs10)) gammaZero_mul_self
        (fiE_commute_gammaZero (y433Sigma_lt hs10) (y433_sigma_ne_eight s hs10 hs9))
  · have ht10' : t < 10 := by omega
    have hs10 : s < 10 := by omega
    rw [y433Img_of_lt hs10, y433Img_of_lt ht10', y433_pairExp_lt s hs10 t ht10' hst]
    exact y433M_fiE_cox (y433Sigma_lt hs10) (y433Sigma_lt ht10')
      fun h => absurd (y433Sigma_injOn s hs10 t ht10' h) (by omega)

end CFSG.Monster.Existence
end
