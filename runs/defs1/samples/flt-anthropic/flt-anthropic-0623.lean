open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup

open scoped MatrixGroups

open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup

open scoped MatrixGroups

namespace ModularCurve

noncomputable section

namespace CuspSpace

variable {N : ℕ}

def cuspWidth (x : CuspSpace N) : ℕ := cuspWidthOfDenom N (cuspDenom N x)

end CuspSpace
end
end ModularCurve
