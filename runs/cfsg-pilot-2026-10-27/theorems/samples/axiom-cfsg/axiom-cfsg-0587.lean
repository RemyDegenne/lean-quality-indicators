public section

namespace CFSG.StandardType

open Module CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL CFSG.StandardType.D4Rank CFSG.StandardType.L613KG
  CFSG.Assembly.LowTwoRank QuadraticMap

open scoped Matrix

namespace L613C3

variable {K : Type} [Field K]

section Coord

theorem eq_sum_jf {v : Fin (2 * 4) → K} (h3 : v (jf (Fin.last 3)) = 0) (he : ∀ k, v (ie k) = 0) :
    v = ∑ l : Fin 3, v (jf l.castSucc) • (Pi.single (jf l.castSucc) 1 : Fin (2 * 4) → K) := by
  refine vec_ext (fun m => ?_) ?_ (fun m => ?_) ?_ <;>
    simp only [sum_jf_apply, single_jf_apply_jf, single_jf_apply_ie, Fin.castSucc_inj,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, h3, he,
      Finset.sum_const_zero]
  · simp only [(castSucc_ne_last' _).symm, ite_false, Finset.sum_const_zero]

end Coord
end L613C3
end CFSG.StandardType
end
