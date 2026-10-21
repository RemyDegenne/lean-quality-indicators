namespace OAI

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [CStarAlgebra A]

theorem isometryDilation_selfAdjoint (V : A) : IsSelfAdjoint (isometryDilation V) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [isometryDilation, Matrix.star_apply]

end CoarseAssembly.Analytic
end
end OAI
