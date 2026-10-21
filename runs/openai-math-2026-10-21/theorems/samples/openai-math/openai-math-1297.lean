namespace OAI

section

namespace ExactFourier.DensePair

open scoped Matrix

theorem exchange23 (l : ℂ) : Y2.updateRow 1 (Xb l 1)=Y3 ∧
    (Xb l).updateRow 1 (Y2 1)=X l := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Y2,Y3,X,Xb,Matrix.updateRow_apply]

end ExactFourier.DensePair
end
end OAI
