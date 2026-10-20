@[expose] public section

noncomputable section

open Polynomial

namespace Real

@[inherit_doc] scoped[goldenRatio] notation "φ" => Real.goldenRatio

@[inherit_doc] scoped[goldenRatio] notation "ψ" => Real.goldenConj

open scoped goldenRatio

theorem goldenRatio_lt_two : φ < 2 := by calc
  (1 + √5) / 2 < (1 + 3) / 2 := by gcongr; rw [sqrt_lt'] <;> norm_num
  _ = 2 := by norm_num

end Real
end
end
