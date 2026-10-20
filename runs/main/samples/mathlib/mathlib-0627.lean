@[expose] public section

universe u v

noncomputable section

open scoped unitInterval

open Path ContinuousMap Set.Icc TopologicalSpace

scoped[HSpaces] notation x "⋀" y => HSpace.hmul (x, y)

open scoped HSpaces

namespace unitInterval

theorem qRight_one_left (θ : I) : qRight (1, θ) = 1 :=
  Set.projIcc_of_right_le _ <|
    (le_div_iff₀ <| add_pos zero_lt_one).2 <| by
      dsimp only
      rw [coe_one, one_mul, mul_one, add_comm, ← one_add_one_eq_two]
      simp only [add_le_add_iff_right]
      exact le_one _

end unitInterval
end
end
