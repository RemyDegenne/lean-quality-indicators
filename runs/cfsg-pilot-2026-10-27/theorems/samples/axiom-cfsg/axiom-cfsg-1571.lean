public section

namespace CFSG.StandardType

namespace SUFacts

open CFSG.LieType.Universal.Unitary

open CFSG.LieType.BorelTits (unitaryInvolution)

section Transfer

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {n : ℕ} {G : Type} [Group G]
  {ψ : SU σ n →* G}

omit [CharP F 2] in
theorem finite_of_le_range_SU [Finite F] {K : Subgroup G} (hK : K ≤ ψ.range) : Finite K := by
  have : Finite ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  exact Finite.of_injective (Subgroup.inclusion hK) (Subgroup.inclusion_injective hK)

end Transfer
end SUFacts
end CFSG.StandardType
end
