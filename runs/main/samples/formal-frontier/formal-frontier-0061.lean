@[expose] public section

universe u v

open UniformSpace

namespace Valued

theorem isValuativeTopology_ofValuation {R : Type u} [Ring R] {Γ₀ : Type v}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued R Γ₀] :
    @IsValuativeTopology R _ (ValuativeRel.ofValuation hv.v)
      hv.toUniformSpace.toTopologicalSpace := by
  letI : ValuativeRel R := ValuativeRel.ofValuation hv.v
  letI : hv.v.Compatible := Valuation.Compatible.ofValuation hv.v
  exact IsValuativeTopology.of_mem_nhds_zero_iff_vle hv.v
    (fun {s} => Valued.mem_nhds_zero)

end Valued
end
