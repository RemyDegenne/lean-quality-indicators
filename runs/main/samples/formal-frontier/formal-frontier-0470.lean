@[expose] public section

universe u v w

namespace PrimeSpectrum

variable (R : Type u) [CommRing R] [IsDomain R]

theorem isOpen_iff_eq_empty_or_bot_mem [Finite (PrimeSpectrum R)]
    [Ring.KrullDimLE 1 R] (s : Set (PrimeSpectrum R)) :
    IsOpen s ↔ s = ∅ ∨ (⊥ : PrimeSpectrum R) ∈ s := by
  constructor
  · intro hs
    by_cases h : s = ∅
    · exact Or.inl h
    · right
      obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr h
      exact (specializes_iff_forall_open.mp
        ((PrimeSpectrum.le_iff_specializes _ _).mp bot_le)) s hs hp
  · rintro (rfl | hbot)
    · exact isOpen_empty
    · have hclosed : IsClosed (sᶜ) := by
        have hclosed' : IsClosed
            (⋃ p : {p : PrimeSpectrum R // p ∉ s}, {p.1}) := by
          apply isClosed_iUnion
          intro p
          apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal p.1).mpr
          apply Ideal.IsPrime.isMaximal_of_ne_bot p.1.isPrime
          intro h
          have hp : p.1 = ⊥ := PrimeSpectrum.ext (by simpa using h)
          exact p.2 (hp ▸ hbot)
        convert hclosed' using 1
        ext p
        simp
      exact isClosed_compl_iff.mp hclosed

end PrimeSpectrum
end
