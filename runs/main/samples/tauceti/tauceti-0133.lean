public section

namespace TauCeti

open NumberField IsDedekindDomain nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

namespace MultiplicativeIdealWeight

@[ext]
theorem ext {χ ψ : MultiplicativeIdealWeight K} (h : ∀ I, χ I = ψ I) : χ = ψ :=
  DFunLike.ext _ _ h

end MultiplicativeIdealWeight
end TauCeti
end
