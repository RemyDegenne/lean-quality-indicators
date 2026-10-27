public section

namespace CFSG.RankThree.GF2n.Stroth80.FieldModel

open scoped commutatorElement Matrix

open Polynomial CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim79

variable {G : Type} [Group G] [Finite G] {M V Q : Subgroup G}

section PolyLemmas

theorem coeff_liftPoly (m : (ZMod 2)[X]) (i : ℕ) : (liftPoly m).coeff i = (m.coeff i).val := by
  simp only [liftPoly, finset_sum_coeff, coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with h
  · rfl
  · have : m.natDegree < i := by omega
    rw [coeff_eq_zero_of_natDegree_lt this]
    simp

end PolyLemmas
end CFSG.RankThree.GF2n.Stroth80.FieldModel
end
