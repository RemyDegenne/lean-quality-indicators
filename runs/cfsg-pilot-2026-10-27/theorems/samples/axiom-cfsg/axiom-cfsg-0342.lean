public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup

open scoped commutatorElement

section FConstruction

variable {N Y : Type} [Group N] [Group Y]

variable {V : Subgroup N} {q : N →* Y} {ρ : Y →* MulAut V} {S1 S2 : Subgroup Y}
  {D1 D2 : Subgroup V} {z : N}

namespace FSetup

variable (h : FSetup V q ρ S1 S2 D1 D2 z)

include h

variable [Finite N] in
theorem exists_F : ∃ F : Subgroup N, Nat.card F = 2 ^ 10 * 315 ∧
    (∀ a ∈ F, ∀ b ∈ F, a * (z * b * z⁻¹) = (z * b * z⁻¹) * a) ∧
    ∀ a ∈ F, z * a * z⁻¹ ∈ F → a = 1 := by
  set F := ⁅S1.comap q, S1.comap q⁆ with hF
  have hz1 : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.hz
  have hFS : F ≤ S1.comap q := F_le
  have hzS : ∀ a ∈ S1.comap q, z * a * z⁻¹ ∈ S2.comap q := fun a ha => by
    rw [mem_comap, map_mul, map_mul, map_inv]
    exact h.hz12 _ ha
  have hzV : ∀ u : V, z * (u : N) * z⁻¹ ∈ V := fun u => by
    rw [← h.hρ z u]
    exact (ρ (q z) u).2
  have hconj : ∀ w : N, z * (z * w * z⁻¹) * z⁻¹ = w := fun w => by
    calc z * (z * w * z⁻¹) * z⁻¹ = (z * z) * w * (z * z)⁻¹ := by group
      _ = w := by rw [h.hz]; group
  have hzS' : ∀ a ∈ S1.comap q, z⁻¹ * a * z ∈ S2.comap q := fun a ha => by
    rw [show z⁻¹ * a * z = z * a * z⁻¹ by rw [hz1]]
    exact hzS a ha
  have KF : ∀ x ∈ F, ∀ f ∈ F, x = z * f * z⁻¹ → x = 1 := by
    intro x hx f hf hxf
    have hq1 : q x ∈ S1 := hFS hx
    have hq2 : q x ∈ S2 := by
      have : x ∈ S2.comap q := by rw [hxf]; exact hzS f (hFS hf)
      exact this
    have hq : q x = 1 := by
      have : q x ∈ S1 ⊓ S2 := ⟨hq1, hq2⟩
      rw [disjoint_iff.1 h.hdisj, Subgroup.mem_bot] at this
      exact this
    have hxV : x ∈ V := h.mem_V_of_q_eq_one hq
    obtain ⟨u1, hu1, hu1x⟩ := h.F_inf_V hx hxV
    have hfV : f ∈ V := by
      have := hzV ⟨x, hxV⟩
      have e1 : f = z * x * z⁻¹ := by rw [hxf]; exact (hconj f).symm
      rw [e1]
      exact this
    obtain ⟨u2, hu2, hu2f⟩ := h.F_inf_V hf hfV
    have hx2 : x = ((ρ (q z) u2 : V) : N) := by
      rw [h.hρ z u2, show (u2 : N) = f from hu2f, hxf]
    have hu12 : u1 = ρ (q z) u2 := V.subtype_injective (hu1x.trans hx2)
    have hbot : u1 ∈ D1 ⊓ D2 := ⟨hu1, hu12 ▸ h.hzD12 u2 hu2⟩
    rw [h.hDinf, Subgroup.mem_bot] at hbot
    rw [← hu1x, hbot]
    rfl
  refine ⟨F, by rw [h.card_F]; norm_num, ?_, ?_⟩
  · intro a ha b hb
    set b' := z * b * z⁻¹ with hb'
    have hb'S : b' ∈ S2.comap q := hzS b (hFS hb)
    have hA : b' * a⁻¹ * b'⁻¹ ∈ F := h.F_conj_S2 hb'S (inv_mem ha)
    have ha'S : z⁻¹ * a * z ∈ S2.comap q := hzS' a (hFS ha)
    have hB : (z⁻¹ * a * z) * b * (z⁻¹ * a * z)⁻¹ ∈ F := h.F_conj_S2 ha'S hb
    have hx : a * b' * a⁻¹ * b'⁻¹ = 1 := by
      refine KF _ (by
        have : a * b' * a⁻¹ * b'⁻¹ = a * (b' * a⁻¹ * b'⁻¹) := by group
        rw [this]
        exact mul_mem ha hA) ((z⁻¹ * a * z) * b * (z⁻¹ * a * z)⁻¹ * b⁻¹)
        (mul_mem hB (inv_mem hb)) ?_
      rw [hb']
      group
    calc a * b' = a * b' * a⁻¹ * b'⁻¹ * (b' * a) := by group
      _ = b' * a := by rw [hx, one_mul]
  · intro a ha haz
    have h1 := KF _ haz a ha rfl
    calc a = z⁻¹ * (z * a * z⁻¹) * z := by group
      _ = 1 := by rw [h1]; group

end FSetup
end FConstruction
end CFSG.EvenSporadicStandard.M24Std.DRes
end
