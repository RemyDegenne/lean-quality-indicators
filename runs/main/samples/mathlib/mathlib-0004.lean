@[expose] public section

noncomputable section

open Polynomial

namespace Real

@[inherit_doc] scoped[goldenRatio] notation "φ" => Real.goldenRatio

@[inherit_doc] scoped[goldenRatio] notation "ψ" => Real.goldenConj

open scoped goldenRatio

theorem goldenRatio_irrational : Irrational φ := by
  have := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  have := this.ratCast_add 1
  convert this.ratCast_mul (show (0.5 : ℚ) ≠ 0 by norm_num)
  simp
  ring

end Real
end
end
