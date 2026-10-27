public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LieType.Steinberg
  Multiplicative

section Weyl

variable {k : Type*} [Field k]

theorem sl2_weyl_eq {β : k} (hβ : β ≠ 0) :
    sl2Upper β * sl2Lower (-β⁻¹) * sl2Upper β = sl2Lower (-β⁻¹) * sl2Upper β * sl2Lower (-β⁻¹) := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Lower, coe_sl2Upper, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hβ]

end Weyl
end CFSG.HardMathSupport.Timmesfeld.CrossChar
end
