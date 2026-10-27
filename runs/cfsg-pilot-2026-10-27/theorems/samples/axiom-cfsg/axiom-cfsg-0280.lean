public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E

namespace Datum

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V] (D : Datum V)

theorem A_inter_conj_eq_zero (hN1 : ∀ a ∈ D.A, a ≠ 0 → ∀ w ∈ D.W, (w a = a ∨ w a = -a) →
      ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q)
    (hN2 : ∀ w ∈ D.W, (∀ a ∈ D.A, w a ∈ D.A) → ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q)
    {x : V ≃ₗ[ZMod 3] V} (hxW : x ∈ D.W) (hcomm : D.tp x * D.t = D.t * D.tp x)
    (hne : D.tp x ≠ D.t) {a : V} (haA : a ∈ D.A) (haA' : a ∈ img x⁻¹ D.A) : a = 0 := by
  by_contra ha0
  have hxa : x a ∈ D.A := mem_img_inv.1 haA'
  have hxa0 : x a ≠ 0 := fun h => ha0 (by simpa using h)
  have hQ : ∀ q ∈ D.Q, ∀ q' ∈ conjSub x D.Q, q * q' * q⁻¹ ∈ conjSub x D.Q := by
    intro q hq q' hq'
    obtain ⟨r, hr, rfl⟩ := hq'
    have hw : x * q * x⁻¹ ∈ D.W := D.W.mul_mem (D.W.mul_mem hxW (D.Q_le_W hq)) (D.W.inv_mem hxW)
    have hwa : (x * q * x⁻¹) (x a) = x a ∨ (x * q * x⁻¹) (x a) = -(x a) := by
      left
      have h1 : (x * q * x⁻¹) (x a) = x (q a) := by
        simp [LinearEquiv.mul_apply]
      rw [h1, D.Q_fix_A q hq a haA]
    have := hN1 (x a) hxa hxa0 _ hw hwa r hr
    refine ⟨_, this, ?_⟩
    show x⁻¹ * (x * q * x⁻¹ * r * (x * q * x⁻¹)⁻¹) * x⁻¹⁻¹ = q * (x⁻¹ * r * x) * q⁻¹
    group
  have ht'comm : ∀ q ∈ D.Q, q * D.tp x = D.tp x * q := by
    intro q hq
    have hs : q⁻¹ * D.tp x * q ∈ conjSub x D.Q := by
      have := hQ q⁻¹ (D.Q.inv_mem hq) (D.tp x) (D.tp_mem x)
      simpa using this
    have hs2 : (q⁻¹ * D.tp x * q) * (q⁻¹ * D.tp x * q) = 1 := by
      have : (q⁻¹ * D.tp x * q) * (q⁻¹ * D.tp x * q) = q⁻¹ * (D.tp x * D.tp x) * q := by group
      rw [this, D.tp_mul_self]; group
    rcases D.tp_unique x _ hs hs2 with h | h
    · exact absurd (by
        have : D.tp x = q * 1 * q⁻¹ := by rw [← h]; group
        simpa using this) (D.tp_ne_one x)
    · calc q * D.tp x = q * (q⁻¹ * D.tp x * q) := by rw [h]
        _ = D.tp x * q := by group
  have hYQ : ∀ q ∈ D.Q, ∀ v ∈ img x⁻¹ D.A, q v ∈ img x⁻¹ D.A := by
    intro q hq v hv
    rw [D.tp_apply_iff_A] at hv ⊢
    have h1 : D.tp x (q v) = q (D.tp x v) := by
      have := congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) (ht'comm q hq)
      simpa using this.symm
    rw [h1, hv]
  have hYt : ∀ v ∈ img x⁻¹ D.A, D.t v ∈ img x⁻¹ D.A := by
    intro v hv
    rw [D.tp_apply_iff_A] at hv ⊢
    have h1 : D.tp x (D.t v) = D.t (D.tp x v) := by
      have := congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) hcomm
      simpa using this
    rw [h1, hv]
  have hYF : ∀ f ∈ img x⁻¹ D.A, f ∈ D.F → f = 0 := by
    intro f hfY hfF
    by_contra hf0
    have hFY : ∀ g ∈ D.F, g ∈ img x⁻¹ D.A :=
      D.F_le_of_Q_closed (img x⁻¹ D.A).toAddSubgroup hYQ hfY hfF hf0
    have hFle : D.F ≤ img x⁻¹ D.A := fun g hg => hFY g hg
    have hFeq : D.F = img x⁻¹ D.A :=
      submodule_eq_of_le_card hFle (by rw [card_img_A, D.card_F])
    have : a ∈ D.F := by rw [hFeq]; exact haA'
    exact ha0 (D.inter_eq_zero haA this)
  have hYA : img x⁻¹ D.A ≤ D.A := by
    intro y hy
    obtain ⟨a', ha'Y, ha'A, f, hfY, hfF, hyeq⟩ :=
      D.split_of_t_closed (img x⁻¹ D.A).toAddSubgroup hYt hy
    have := hYF f hfY hfF
    rw [hyeq, this, add_zero]; exact ha'A
  have hAeq : img x⁻¹ D.A = D.A := submodule_eq_of_le_card hYA (by rw [D.card_A, card_img_A])
  have hxinvA : ∀ a' ∈ D.A, x⁻¹ a' ∈ D.A := fun a' ha' => hAeq ▸ (mem_img.2 ⟨a', ha', rfl⟩)
  have hxinvW : x⁻¹ ∈ D.W := D.W.inv_mem hxW
  have h2 := hN2 x⁻¹ hxinvW hxinvA D.t D.t_mem
  have h3 : D.tp x ∈ D.Q := by
    have : x⁻¹ * D.t * x⁻¹⁻¹ = D.tp x := by unfold tp; simp
    rwa [this] at h2
  rcases D.t_unique _ h3 (D.tp_mul_self x) with h | h
  · exact D.tp_ne_one x h
  · exact hne h

end Datum
end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E
end
