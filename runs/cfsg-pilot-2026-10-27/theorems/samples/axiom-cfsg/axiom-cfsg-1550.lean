public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

open scoped commutatorElement

theorem mulAut_conj_comm_apply {S : Type} [Group S] (β : MulAut S) (y : S) :
    MulAut.conj (β y) * β = β * MulAut.conj y := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, mul_assoc]

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
end
