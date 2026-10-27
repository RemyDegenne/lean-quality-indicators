public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.UC22.F07

open CFSG.LocalAnalysis.UniquenessCase.PartTwo

open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_three_of_counter (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p)
    (h3 : R17_3At D V₀ V) (h55 : R17_55At D V₀ V)
    (h59 : R17_59At D V₀ V) (h63 : UC6.R6_3 D)
    {K : Subgroup G} (hK : K ∈ calC (Lp D p))
    {n : ℕ} (hnodd : Odd n) (hKshape : IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n) :
    n = 3 := by
  have hn2 : 2 ≤ n := by
    rcases hKshape with h | h
    · exact s13_two_le_of_isL2 h
    · have := (s13_odd_three_le_of_isSz h).2
      omega
  exact CFSG.eq_three_of_forall_prime_dvd_two_pow_sub_one n hnodd hn2
    (fun r hr hrd => prime_dvd_two_pow_sub_one_eq_seven D ctx h3 h55 h59 h63
      hK hnodd hKshape hr hrd)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
end
