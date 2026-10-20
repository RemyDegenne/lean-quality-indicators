@[expose] public section

universe uR uM uN

namespace Module

variable (R : Type uR) (M : Type uM)

variable [Semiring R] [AddCommMonoid M] [Module R M]

namespace CountablyGenerated

variable {R M}

theorem of_finite [Module.Finite R M] : Module.CountablyGenerated R M := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  refine ⟨fun i ↦ if hi : i < n then s ⟨i, hi⟩ else 0, ?_⟩
  apply top_unique
  rw [← hs]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨i, by simp [i.isLt]⟩

end CountablyGenerated
end Module
end
