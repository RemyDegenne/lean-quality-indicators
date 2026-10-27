@[expose] public section

namespace Valuation.IsRankOneDiscrete

open WithZero MonoidWithZeroHom NNReal WithZeroMulInt

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

section Ring

variable {R : Type*} [Ring R]

section LinearOrderedCommGroupWithZero

variable (v : Valuation R Γ) [hv : v.IsRankOneDiscrete]

/-- A discrete valuation has rank one. -/
@[instance_reducible]
noncomputable def rankOne {e : ℝ≥0} (he : 1 < e) : v.RankOne where
  hom' := (toNNReal (ne_of_gt (lt_trans zero_lt_one he))).comp (valueGroup₀_equiv_withZeroMulInt v)
  strictMono' := (toNNReal_strictMono he).comp (valueGroup₀_equiv_withZeroMulInt_strictMono v)
  exists_val_nontrivial := IsNontrivial.exists_val_nontrivial

end LinearOrderedCommGroupWithZero
end Ring
end Valuation.IsRankOneDiscrete
end
