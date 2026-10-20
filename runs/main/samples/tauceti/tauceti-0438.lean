public section

open Filter MulAction Set Topology TauCeti.Subgroup.CuspDatum UpperHalfPlane

open scoped MatrixGroups Pointwise

namespace Subgroup

namespace CompactifiedQuotient

variable {Γ : Subgroup PSL(2, ℝ)}

variable (D : Γ.CuspDatum) (A : ℝ)

variable [DiscreteTopology Γ]

theorem isOpenEmbedding_ofQuotient : IsOpenEmbedding (ofQuotient (Γ := Γ)) :=
  .of_continuous_injective_isOpenMap continuous_ofQuotient ofQuotient_injective
    isOpenMap_ofQuotient

end CompactifiedQuotient
end Subgroup
end
