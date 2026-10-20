@[expose] public section

namespace Valuation

open LinearOrderedCommGroup MonoidWithZeroHom Set Subgroup

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

section Ring

variable {A : Type*} [Ring A] (v : Valuation A Γ)

namespace IsRankOneDiscrete

variable [IsRankOneDiscrete v]

@[simp]
lemma embedding_generator' :
    ValueGroup₀.embedding (f := (v : A →*₀ Γ)) (generator' v) = generator v := rfl

end IsRankOneDiscrete
end Ring
end Valuation
end
