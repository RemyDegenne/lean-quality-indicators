section case2

section eisenstein

open NumberField IsCyclotomicExtension.Rat.Three

variable {K : Type*} [Field K]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

local notation3 "η" => (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit

local notation3 "λ" => hζ.toInteger - 1

namespace FermatLastTheoremForThreeGen

variable {hζ}

variable (S : Solution hζ) (S' : Solution' hζ)

namespace Solution

variable [NumberField K] [IsCyclotomicExtension {3} ℚ K]

attribute [local instance] IsCyclotomicExtension.Rat.three_pid

/-- Let `u₄ := η * S.u₃ * S.u₂⁻¹` -/
noncomputable def u₄ := η * S.u₃ * S.u₂⁻¹

end Solution
end FermatLastTheoremForThreeGen
end eisenstein
end case2
