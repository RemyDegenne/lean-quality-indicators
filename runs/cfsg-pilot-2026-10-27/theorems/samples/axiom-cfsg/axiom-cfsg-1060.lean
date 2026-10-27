public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo CFSG.Fischer Matrix

open scoped commutatorElement

namespace U52

theorem Acoord_mul (a c d e a' c' d' e' : F4) :
    Acoord a c d e * Acoord a' c' d' e' =
      Acoord (a + a') (c + c') (d + d') (e + e' + bar d * d' + a' * bar c + bar a' * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Acoord, x₂Mat, x₃Mat, x₄Mat, Matrix.mul_apply, Fin.sum_univ_five]
  all_goals linear_combination (-(bar a' * c)) * CFSG.Fischer.F4.two_eq_zero

end U52
end CFSG.LocalAnalysis.GLTheoremA.CatB
end
