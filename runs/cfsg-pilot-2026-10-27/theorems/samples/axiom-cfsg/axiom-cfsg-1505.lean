public section

namespace CFSG.LieType.SeitzGeneration

section Arith

variable {K : Type*} [Field K] {r : ℕ} [Fact r.Prime]

local notation "χ" => quadraticChar (ZMod r)

theorem ug87_chi_cases (x : ZMod r) : χ x = 0 ∨ χ x = 1 ∨ χ x = -1 := by
  by_cases hx : x = 0
  · exact Or.inl (by rw [hx]; exact quadraticChar_zero)
  · exact Or.inr (quadraticChar_dichotomy hx)

end Arith
end CFSG.LieType.SeitzGeneration
end
