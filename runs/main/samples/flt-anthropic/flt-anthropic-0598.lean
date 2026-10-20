namespace P2MW.S_IsRegularLocalRing_spanFinrank_ker_add_ringKrullDim_eq

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option synthInstance.maxHeartbeats 1600000

open IsLocalRing

noncomputable section

namespace RSMU

section CotImage

variable {A : Type*} [CommRing A] [IsLocalRing A]

theorem exists_eq_toCotangent_of_mem_cotSpan {ι : Type*} {z : ι → ↥(maximalIdeal A)} {u : CotangentSpace A}
    (hu : u ∈ cotSpan z) :
    ∃ y : ↥(maximalIdeal A), (y : A) ∈ idealSpan z ∧ (maximalIdeal A).toCotangent y = u := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨z i, Ideal.subset_span ⟨i, rfl⟩, rfl⟩
  | zero => exact ⟨0, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, (idealSpan z).add_mem ha hb, by simp⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨c • a, ?_, ?_⟩
    · rw [Submodule.coe_smul, smul_eq_mul]; exact (idealSpan z).mul_mem_left c ha
    · rw [map_smul]; exact (residue_smul_eq c _).symm

end CotImage
end RSMU
end
end P2MW.S_IsRegularLocalRing_spanFinrank_ker_add_ringKrullDim_eq
