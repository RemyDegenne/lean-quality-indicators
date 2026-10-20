@[expose] public section

noncomputable section

variable {α : Type*}

open NNReal ENNReal MeasureTheory

namespace PMF

theorem hasSum_coe_one (p : PMF α) : HasSum p 1 :=
  p.2

end PMF
end
end
