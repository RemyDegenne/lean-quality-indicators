@[expose] public section

universe u v

namespace Module.End

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

theorem isUnit_of_sub_mem_smul (I : Ideal R) [IsAdicComplete I M]
    (f : Module.End R M) (hf : ∀ m, f m - m ∈ I • (⊤ : Submodule R M)) :
    IsUnit f := by
  have hq : Function.Surjective ((I • (⊤ : Submodule R M)).mkQ.comp f) := by
    intro q
    obtain ⟨m, rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective q
    refine ⟨m, ?_⟩
    exact (Submodule.Quotient.eq _).2 (hf m)
  exact (Module.End.isUnit_iff f).2
    ⟨Module.End.injective_of_sub_mem_smul (I := I) (f := f) hf,
      surjective_of_mkQ_comp_surjective (I := I) (f := f) hq⟩

end Module.End
end
