namespace P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq

set_option autoImplicit false

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace WeierstrassCurve

namespace VCTransport

p2m_open

p2m_open

variable {k : Type*} [Field k] [DecidableEq k]

theorem conj_mem_rationalHomSet (C : VariableChange k) (X : WeierstrassCurve k)
    {α : (X⁄k).Point →+ (X⁄k).Point} (hα : α ∈ rationalHomSet k X X) :
    (endConj (variableChangeAddEquiv C X) α : ((C • X)⁄k).Point →+ ((C • X)⁄k).Point) ∈ rationalHomSet k (C • X) (C • X) := by
  rcases hα with rfl | hα
  · left; ext P; rfl
  right
  have hu : (C.u : k) ≠ 0 := C.u.ne_zero
  refine isRationallyRepresented_conj (W₁ := X) (W₂ := C • X) hα (vcFun C X) (vcInvFun C X)
    ((C.u : k) ^ 2) C.r ((C.u : k) ^ 3) ((C.u : k) ^ 2 * C.s) C.t
    (((C.u⁻¹ : kˣ) : k) ^ 2) (-(((C.u⁻¹ : kˣ) : k) ^ 2 * C.r)) (((C.u⁻¹ : kˣ) : k) ^ 3) (-(((C.u⁻¹ : kˣ) : k) ^ 3 * C.s))
    (((C.u⁻¹ : kˣ) : k) ^ 3 * (C.s * C.r - C.t)) (pow_ne_zero _ hu) ?_ ?_ fun P => rfl
  · intro x y h
    exact ⟨(nonsingular_variableChange_iff x y).mp h, rfl⟩
  · intro x y h
    refine ⟨?_, ?_⟩
    swap
    · show Point.some (vcXInv C x) (vcYInv C x y) _ = _
      apply some_eq_some'' <;> simp only [vcXInv, vcYInv] <;> first | ring | skip
    · have h' : X.toAffine.Nonsingular (vcX C (vcXInv C x)) (vcY C (vcXInv C x) (vcYInv C x y)) := by
        rw [vcX_vcXInv, vcY_vcYInv]; exact h
      have h'' := (nonsingular_variableChange_iff (C := C) (W := X) _ _).mpr h'
      convert h'' using 1 <;> first | rfl | ring1 | (simp only [vcXInv, vcYInv, Units.val_inv_eq_inv_val]; ring1) | (simp only [vcXInv, vcYInv]; ring1)
where
  some_eq_some'' {W' : WeierstrassCurve.Affine k} {x₁ y₁ x₂ y₂ : k} {h₁ : W'.Nonsingular x₁ y₁} {h₂ : W'.Nonsingular x₂ y₂}
      (hx : x₁ = x₂) (hy : y₁ = y₂) : Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by subst hx hy; rfl

end VCTransport
end WeierstrassCurve
end P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq
