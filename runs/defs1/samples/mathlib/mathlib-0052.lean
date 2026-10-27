@[expose] public section

variable {R S M N : Type*}

variable (S) [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]

variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]

variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]

variable (M' M'' : Submodule R M)

namespace Submodule

/-- The Galois insertion between `Submodule R M` and `Submodule S N`,
where `S` is the localization of `R` at `p` and `N` is the localization of `M` at `p`. -/
def localized'gi : GaloisInsertion (localized' S p f) (comap f <| ·.restrictScalars R) where
  gc M' N' := ⟨fun h m hm ↦ h ⟨m, hm, 1, by simp⟩, fun h ↦ by
    rw [localized'_eq_span, span_le]; apply map_le_iff_le_comap.mpr h⟩
  le_l_u N' n hn := by
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f n
    refine ⟨m, ?_, s, rfl⟩
    rw [mem_comap, restrictScalars_mem, ← IsLocalizedModule.mk'_cancel' _ _ s,
      Submonoid.smul_def, ← algebraMap_smul S]
    exact smul_mem _ _ hn
  choice x _ := localized' S p f x
  choice_eq _ _ := rfl

end Submodule
end
