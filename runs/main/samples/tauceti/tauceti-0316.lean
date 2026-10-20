public section

noncomputable section

open NumberField

open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

@[simp]
theorem mem_maximalOrderFractionalIdealEquiv
    {I : FractionalIdeal (maximalNumberFieldOrder K).toSubalgebra⁰ K} {x : K} :
    x ∈ maximalOrderFractionalIdealEquiv K I ↔ x ∈ I := by
  have h (y : K) : IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K)
      (maximalOrderRingEquiv K) y = y := by
    rw [ringEquivOfRingEquiv_maximalOrderRingEquiv, RingEquiv.refl_apply]
  rw [← FractionalIdeal.mem_coe, maximalOrderFractionalIdealEquiv,
    FractionalIdeal.ringEquivOfRingEquiv_apply, FractionalIdeal.coe_mk]
  simp only [Submodule.mem_map, FractionalIdeal.val_eq_coe, FractionalIdeal.mem_coe]
  -- The semilinear equivalence underlying the transport applies
  -- `IsFractionRing.ringEquivOfRingEquiv` (`IsFractionRing.semilinearEquivOfRingEquiv_apply`).
  refine ⟨fun ⟨y, hy, hyx⟩ => ?_, fun hx => ⟨x, hx, h x⟩⟩
  obtain rfl : y = x := (h y).symm.trans hyx
  exact hy

end TauCeti.GlobalNumberFields
end
end
