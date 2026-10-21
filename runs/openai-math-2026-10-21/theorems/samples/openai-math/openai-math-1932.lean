namespace OAI

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal CStarAlgebra

namespace Invariant233

variable {A : Type*} [CStarAlgebra A]

theorem fugledeKadisonDeterminant_pos_of_isUnit (τ : TracialState A) (a : A)
    (ha : IsUnit a) : 0 < fugledeKadisonDeterminant τ a := by
  rw [fugledeKadisonDeterminant_of_isUnit τ a ha]
  exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)

end Invariant233
end
end OAI
