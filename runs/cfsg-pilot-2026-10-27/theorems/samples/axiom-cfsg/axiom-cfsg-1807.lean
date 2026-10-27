public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryFrame

variable {ℓ f n m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

variable {h}

section Glue

theorem frameMat_mul_apply (u : Fin m → Fin n → K) (W : Matrix (Fin m) (Fin m) K) (k : Fin n)
    (i : Fin m) : (frameMat u * W) k i = (frameMat u *ᵥ fun j => W j i) k := rfl

end Glue
end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo
end
