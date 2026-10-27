public section

namespace CFSG.StandardType

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

namespace InnerDiagSU

section TwoByTwo

variable {F : Type*} [Field F] [CharP F 2]

theorem block_identity :
    !![1, 0; 1, 1] * !![1, 1; 0, 1] * !![1, 0; 1, 1] * !![(1 : F), 1; 0, 1] =
      !![1, 1; 0, 1] * !![1, 0; 1, 1] * !![1, 1; 0, 1] * !![(1 : F), 1; 0, 1] := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linear_combination h2

end TwoByTwo
end InnerDiagSU
end CFSG.StandardType
end
