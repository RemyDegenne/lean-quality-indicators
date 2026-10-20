public section

namespace TauCeti

universe u v w

namespace IntegralLattice

variable {V : Type u} {W : Type v} {U : Type w}

variable [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

variable [AddCommGroup U] [Module ℚ U]

section OrthogonalSum

variable (L : IntegralLattice V) (M : IntegralLattice W)

variable {L M}

@[simp]
theorem orthogonalSumIntermediateCarrier_bot :
    orthogonalSumIntermediateCarrier L M ⊥ ⊥ = ⊥ := by
  refine Subtype.ext (Submodule.ext fun p ↦ ?_)
  rw [mem_orthogonalSumIntermediateCarrier_iff, Set.Icc.coe_bot, Set.Icc.coe_bot,
    Set.Icc.coe_bot, orthogonalSum_carrier, Submodule.mem_prod]

end OrthogonalSum
end IntegralLattice
end TauCeti
end
