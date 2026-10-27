set_option linter.unusedSectionVars false

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.RankThree.PartTwo.Sec4.Item434G28

attribute [local irreducible] txL tU tZ tO tzc gW

section VSub

variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

theorem zE_sq : zE M * zE M = (zE M)⁻¹ :=
  eq_inv_of_mul_eq_one_left ((pow_three' (zE M)).symm.trans (zE_pow_three M))

end VSub
end CFSG.AGLEmbedding.KFactProofs.G28
end
