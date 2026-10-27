@[expose] public section

namespace unitInterval

/-- `zeroOneIncl` -/
abbrev zeroOneIncl : C(zeroOne, I) where
  toFun := fun ⟨x, hx⟩ ↦ ⟨x, by
    simp only [Set.mem_Icc]
    obtain hx | hx := hx
    all_goals subst hx; norm_num ⟩
  continuous_toFun := by fun_prop

end unitInterval
end
