public section

namespace GradedAlgebra

universe u v

variable {A : Type u} [CommRing A]

variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]

variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem irrelevant_le_span_of_adjoin_eq_top (s : Set A)
    (hhom : ∀ x ∈ s, ∃ n ≠ 0, x ∈ 𝒜 n)
    (hgen : Algebra.adjoin (𝒜 0) s = ⊤) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span s := by
  intro x hx
  convert_to x - GradedRing.projZeroRingHom 𝒜 x ∈ _
  · rw [GradedRing.projZeroRingHom_apply, ← GradedRing.proj_apply,
      (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx, sub_zero]
  clear hx
  have hx : x ∈ Algebra.adjoin (𝒜 0) s := by rw [hgen]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨n, hn, hxn⟩ := hhom x hx
      rw [GradedRing.projZeroRingHom_apply,
        DirectSum.decompose_of_mem_ne 𝒜 hxn hn, sub_zero]
      exact Ideal.subset_span hx
  | algebraMap r =>
      convert! Ideal.zero_mem (Ideal.span s)
      rw [sub_eq_zero]
      exact (DirectSum.decompose_of_mem_same 𝒜 r.2).symm
  | add x y _ _ _ _ =>
      rw [map_add, add_sub_add_comm]
      exact Ideal.add_mem _ ‹_› ‹_›
  | mul x y _ _ hx' hy' =>
      convert!
        Ideal.add_mem _ (Ideal.mul_mem_left _ x hy')
          (Ideal.mul_mem_right (GradedRing.projZeroRingHom 𝒜 y) _ hx') using 1
      rw [map_mul]
      ring

end GradedAlgebra
end
