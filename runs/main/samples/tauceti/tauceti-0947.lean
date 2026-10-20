public section

open scoped Matrix

namespace TauCeti

section RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic]

theorem isG2_of_hasCartanType_G2 [P.IsReduced] [P.IsIrreducible] {b : P.Base}
    (h : HasCartanType P b .G2) : P.IsG2 := by
  obtain ⟨e, he⟩ : ∃ e : b.support ≃ Fin 2, ∀ i j,
      b.cartanMatrix i j = (!![2, -1; -3, 2] : Matrix (Fin 2) (Fin 2) ℤ) (e i) (e j) := by
    obtain ⟨e, he⟩ := (hasCartanType_iff b .G2).mp h
    exact ⟨e, fun i j ↦ by rw [he i j, DynkinType.cartanMatrix_G2_eq]; rfl⟩
  refine (RootPairing.isG2_iff P).mpr ⟨e.symm 1, e.symm 0, ?_⟩
  have hentry := he (e.symm 1) (e.symm 0)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hentry
  simpa [RootPairing.Base.cartanMatrixIn_def] using hentry

end RootPairing
end TauCeti
end
