@[expose] public section

variable {R V V' P P' : Type*}

open AffineEquiv AffineMap

namespace AffineSubspace

section LinearOrderedField

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [AddTorsor V P]

theorem setOfPred_sOppSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
    { y | s.SOppSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Iio 0) s := by
  ext y
  simp_rw [Set.mem_ofPred, Set.mem_image2, Set.mem_Iio]
  constructor
  · rw [sOppSide_iff_exists_left hp]
    rintro ⟨-, hy, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hy (h ▸ hp₂))
    · refine ⟨-r₁ / r₂, div_neg_of_neg_of_pos (Left.neg_neg_iff.2 hr₁) hr₂, p₂, hp₂, ?_⟩
      rw [div_eq_inv_mul, ← smul_smul, neg_smul, h, smul_neg, smul_smul,
        inv_mul_cancel₀ hr₂.ne.symm, one_smul, neg_vsub_eq_vsub_rev, vsub_vadd]
  · rintro ⟨t, ht, p', hp', rfl⟩
    exact sOppSide_smul_vsub_vadd_right hx hp hp' ht

end LinearOrderedField
end AffineSubspace
end
