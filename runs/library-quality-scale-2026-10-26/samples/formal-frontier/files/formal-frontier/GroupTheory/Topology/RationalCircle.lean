/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# The rational circle inside the real and complex circles

The canonical rational-circle inclusion is injective, and every torsion point
of either circle has a rational-circle preimage. These maps and their proofs
follow the formalization in Supernatural Numbers, using Mathlib's quotient
additive groups and circle homeomorphism.
-/

@[expose] public section

namespace AddCircle

noncomputable section

/-- The canonical inclusion from the rational additive circle into the real additive circle. -/
def rationalToReal : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map (AddSubgroup.zmultiples (1 : ℚ))
    (AddSubgroup.zmultiples (1 : ℝ)) (Rat.castHom ℝ).toAddMonoidHom (by
      rw [← AddSubgroup.map_le_iff_le_comap, AddMonoidHom.map_zmultiples]
      simp)

/-- The canonical inclusion acts by casting a rational representative. -/
@[simp] theorem rationalToReal_mk (q : ℚ) :
    rationalToReal (q : AddCircle (1 : ℚ)) = ((q : ℝ) : AddCircle (1 : ℝ)) :=
  rfl

/-- The rational-circle inclusion into the real circle is injective. -/
theorem rationalToReal_injective : Function.Injective rationalToReal := by
  rw [← AddMonoidHom.ker_eq_bot_iff]
  ext x
  constructor
  · intro hx
    obtain ⟨q, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
    rw [AddSubgroup.mem_bot]
    rw [AddMonoidHom.mem_ker] at hx
    change ((q : ℝ) : AddCircle (1 : ℝ)) = 0 at hx
    rw [AddCircle.coe_eq_zero_iff] at hx
    obtain ⟨n, hn⟩ := hx
    rw [zsmul_one] at hn
    apply (QuotientAddGroup.eq_zero_iff q).mpr
    rw [AddSubgroup.mem_zmultiples_iff]
    exact ⟨n, by simpa using Rat.cast_injective hn⟩
  · intro hx
    rw [AddSubgroup.mem_bot] at hx
    rw [AddMonoidHom.mem_ker, hx, map_zero]

/-- The canonical additive inclusion of the rational circle in the unit circle. -/
def rationalToCircle : AddCircle (1 : ℚ) →+ Additive Circle where
  toFun q := Additive.ofMul (AddCircle.toCircle (rationalToReal q))
  map_zero' := by simp
  map_add' x y := by
    change AddCircle.toCircle (rationalToReal (x + y)) =
      AddCircle.toCircle (rationalToReal x) * AddCircle.toCircle (rationalToReal y)
    rw [map_add, AddCircle.toCircle_add]

/-- On rational representatives, the unit-circle inclusion is the usual
real-circle evaluation. -/
@[simp] theorem rationalToCircle_mk (q : ℚ) :
    Additive.toMul (rationalToCircle (q : AddCircle (1 : ℚ))) =
      AddCircle.toCircle ((q : ℝ) : AddCircle (1 : ℝ)) := rfl

/-- The rational-circle inclusion into the unit circle is injective. -/
theorem rationalToCircle_injective : Function.Injective rationalToCircle := by
  intro x y h
  apply rationalToReal_injective
  apply AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
  exact congrArg Additive.toMul h

/-- Every finite-order point of the real additive circle is rational. -/
theorem exists_rational_preimage_of_isOfFinAddOrder
    {u : AddCircle (1 : ℝ)} (hu : IsOfFinAddOrder u) :
    ∃ q : AddCircle (1 : ℚ), rationalToReal q = u := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℝ)) u
  obtain ⟨q, hq⟩ := (AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div).mp hu
  refine ⟨(q : AddCircle (1 : ℚ)), ?_⟩
  rw [rationalToReal_mk]
  simpa using congrArg (fun y : ℝ ↦ (y : AddCircle (1 : ℝ))) hq

end
end AddCircle

namespace Circle

/-- Every finite-order point of the unit circle comes from the rational circle. -/
theorem exists_rational_preimage_of_isOfFinOrder
    {z : Circle} (hz : IsOfFinOrder z) :
    ∃ q : AddCircle (1 : ℚ), Additive.toMul (AddCircle.rationalToCircle q) = z := by
  let e := AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)
  let u : AddCircle (1 : ℝ) := e.symm z
  have heu : u.toCircle = z := by
    rw [← AddCircle.homeomorphCircle_apply (by norm_num : (1 : ℝ) ≠ 0)]
    exact e.apply_symm_apply z
  have hu : IsOfFinAddOrder u := by
    obtain ⟨n, hn, hzn⟩ := hz.exists_pow_eq_one
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, ?_⟩
    apply AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
    rw [AddCircle.toCircle_nsmul, AddCircle.toCircle_zero]
    rw [heu, hzn]
  obtain ⟨q, hq⟩ := AddCircle.exists_rational_preimage_of_isOfFinAddOrder hu
  refine ⟨q, ?_⟩
  change AddCircle.toCircle (AddCircle.rationalToReal q) = z
  rw [hq]
  exact heu

end Circle

end
