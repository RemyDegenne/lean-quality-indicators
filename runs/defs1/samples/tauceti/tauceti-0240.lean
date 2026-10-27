public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups Pointwise

variable {N : ℕ}

namespace CongruenceSubgroup

/-- A Bézout matrix with bottom row `(N, p)`, for `p` coprime to `N`. -/
noncomputable def gamma0Twist (N p : ℕ) (h : Nat.Coprime p N) : SL(2, ℤ) :=
  ((Nat.isCoprime_iff_coprime.mpr h.symm : IsCoprime (N : ℤ) (p : ℤ)).exists_SL2_row 1).choose

end CongruenceSubgroup
end
