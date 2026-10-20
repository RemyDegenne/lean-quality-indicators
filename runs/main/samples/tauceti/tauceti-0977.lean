public section

noncomputable section

open Metric Set

namespace TauCeti

variable {e : ℕ}

theorem card_puncturedDiscPow_preimage_singleton (he : e ≠ 0) (w : ↥(ball (0 : ℂ) 1 \ {0})) :
    Nat.card (puncturedDiscPow he ⁻¹' {w}) = e := by
  classical
  have hζ := Complex.isPrimitiveRoot_exp e he
  have himage : Subtype.val '' (puncturedDiscPow he ⁻¹' {w}) =
      (Polynomial.nthRootsFinset e (w : ℂ) : Set ℂ) := by
    ext z
    rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero he)]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← coe_puncturedDiscPow_apply he, Set.mem_singleton_iff.1 hz]
    · intro hz
      refine ⟨⟨z, (pow_mem_ball_zero_one_diff_singleton_iff he).1 (hz ▸ w.2)⟩, ?_, rfl⟩
      exact Set.mem_singleton_iff.2 (Subtype.ext hz)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (w : ℂ) (Nat.pos_of_ne_zero he)
  rw [← Nat.card_image_of_injective Subtype.val_injective, himage, Nat.card_coe_set_eq,
    Set.ncard_coe_finset, hζ.card_nthRootsFinset_of_pow_eq hα w.2.2]

end TauCeti
end
end
