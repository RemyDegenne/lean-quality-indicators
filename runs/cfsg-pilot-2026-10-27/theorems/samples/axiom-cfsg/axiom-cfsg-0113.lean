public section

namespace CFSG.Walter.J1Recog

open Word

open scoped commutatorElement

theorem matT_eq : matT = Matrix.diagonal diagT := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end CFSG.Walter.J1Recog
end
