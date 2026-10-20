@[expose] public section

open NumberField ComplexEmbedding InfinitePlace Algebra

open scoped ComplexConjugate

namespace NumberField

section maximalRealSubfield

namespace IsCMField

open ComplexEmbedding

variable (K : Type*) [Field K] [CharZero K] [IsCMField K]

local notation3 "K⁺" => maximalRealSubfield K

section complexConj

variable [Algebra.IsIntegral ℚ K]

@[simp]
theorem complexConj_apply_apply (x : K) :
    complexConj K (complexConj K x) = x := by
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  exact isConj_apply_apply (isConj_complexConj K φ) x

end complexConj
end IsCMField
end maximalRealSubfield
end NumberField
end
