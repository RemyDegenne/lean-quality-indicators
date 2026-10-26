/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.CompletionValuation

/-!
# Topology of the completion valuation

The valuation extending a compatible valuation to the completion induces the
completion's given topology. The value group and the original valuative relation
are arbitrary.

The valued-completion uniformity projection records the connection between
Mathlib's valued completion and its uniform completion.
-/

@[expose] public section

open UniformSpace

universe u v

namespace Valued

/-- The uniformity of a valued completion is the completion uniformity of the
original valued field. -/
theorem valuedCompletion_toUniformSpace {K : Type u} [Field K] {Γ₀ : Type v}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] :
    (@Valued.valuedCompletion K _ Γ₀ _ hv).toUniformSpace =
      @Completion.uniformSpace K hv.toUniformSpace := by
  rfl

end Valued

namespace Valuation

variable {K : Type u} {Γ₀ : Type v} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [vr : ValuativeRel K]
    [U : UniformSpace K] [IsUniformAddGroup K] [hvt : IsValuativeTopology K]

/-- The extension of a compatible valuation induces the given uniform completion
topology through its canonical valuative relation. -/
theorem isValuativeTopology_extensionValuation (v : Valuation K Γ₀) [hcompat : v.Compatible] :
    @IsValuativeTopology (@Completion K U) _
      (ValuativeRel.ofValuation
        (Valuation.extensionValuation (vr := vr) (U := U) (hvt := hvt) v))
      (@Completion.uniformSpace K U).toTopologicalSpace := by
  let hv : Valued K Γ₀ := Valued.mk' v
  have hvr : vr = ValuativeRel.ofValuation hv.v := by
    ext x y
    exact (Valuation.vle_iff_le (v := v) (x := x) (y := y)).trans
      (@Valuation.vle_iff_le K _ (ValuativeRel.ofValuation hv.v) Γ₀ _ hv.v
        (Valuation.Compatible.ofValuation hv.v) x y).symm
  have hU : U = hv.toUniformSpace :=
    (Valuation.toUniformSpace_eq v).trans
      (@Valued.toUniformSpace_eq K _ Γ₀ _ hv).symm
  subst vr
  subst U
  have heq := Valuation.extensionValuation_eq_valued (hv := hv)
  let P : Valuation (@Completion K hv.toUniformSpace) Γ₀ → Prop :=
    fun w => @IsValuativeTopology (@Completion K hv.toUniformSpace) _
      (ValuativeRel.ofValuation w)
      (@Completion.uniformSpace K hv.toUniformSpace).toTopologicalSpace
  have hc := Valued.isValuativeTopology_ofValuation
    (hv := @Valued.valuedCompletion K _ Γ₀ _ hv)
  have hcanonical : P (@Valued.extensionValuation K _ Γ₀ _ hv) := by
    simpa only [P, Valued.valuedCompletion_toUniformSpace (hv := hv)] using hc
  exact (congrArg P heq).mpr hcanonical

end Valuation
