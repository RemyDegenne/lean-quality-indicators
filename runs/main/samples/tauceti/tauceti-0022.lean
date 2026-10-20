public section

namespace TauCeti

namespace PreValuationRing

variable {R : Type*} [Monoid R] [PreValuationRing R] {ι : Type*}

theorem exists_forall_dvd [Finite ι] [Nonempty ι] (f : ι → R) : ∃ i, ∀ j, f i ∣ f j := by
  cases nonempty_fintype ι
  obtain ⟨i, -, h⟩ := exists_mem_forall_dvd Finset.univ_nonempty f
  exact ⟨i, fun j ↦ h j (Finset.mem_univ j)⟩

end PreValuationRing
end TauCeti
end
