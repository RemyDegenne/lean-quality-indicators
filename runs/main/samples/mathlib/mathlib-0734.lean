@[expose] public section

open Function Nat

variable {𝕜 α β : Type*} [Fintype α]

namespace Finset

variable {s t : Finset α} {a b : α}

@[simp] lemma dens_le_one : s.dens ≤ 1 := by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  · simpa using dens_le_dens s.subset_univ

end Finset
end
