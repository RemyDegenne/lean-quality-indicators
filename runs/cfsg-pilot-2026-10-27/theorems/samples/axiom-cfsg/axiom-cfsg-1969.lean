public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General Equiv

open scoped Pointwise

section Sections

variable {N : Type*} [Group N]

variable [IsSimpleGroup N]

omit [IsSimpleGroup N] in
theorem nonempty_mulEquiv_of_surjective_of_ne_comm {A : Type*} [Group A] [IsSimpleGroup A]
    {ψ : A →* N} (hψ : Function.Surjective ψ) (hN : ∃ a b : N, a * b ≠ b * a) :
    Nonempty (A ≃* N) := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
  · exact ⟨MulEquiv.ofBijective ψ ⟨(MonoidHom.ker_eq_bot_iff ψ).mp h, hψ⟩⟩
  · refine absurd ⟨fun a b => ?_⟩ (not_subsingleton_of_ne_comm hN)
    obtain ⟨x, rfl⟩ := hψ a
    obtain ⟨y, rfl⟩ := hψ b
    have h1 : ∀ z, ψ z = 1 := fun z => (h ▸ Subgroup.mem_top z : z ∈ ψ.ker)
    rw [h1, h1]

end Sections
end CFSG.Holt.H78
end
