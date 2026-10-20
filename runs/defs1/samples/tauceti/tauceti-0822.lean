public section

namespace TauCeti

namespace DyadicJordanProfile

/-- A single type-II unimodular constituent of even rank `n`. At `n = 0` this is the empty
profile. -/
noncomputable def unimodularTypeII (n : ℕ) (hn : Even n) : DyadicJordanProfile where
  ranks := Finsupp.single 0 n
  typeI := ∅
  typeI_subset_support := by simp
  even_rank_of_notMem_typeI i _ := by
    rcases eq_or_ne i 0 with rfl | hi
    · simpa using hn
    · simp [Finsupp.single_eq_of_ne hi]

end DyadicJordanProfile
end TauCeti
end
