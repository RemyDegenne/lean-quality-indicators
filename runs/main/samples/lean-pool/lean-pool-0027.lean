@[expose] public section

noncomputable section

open Polynomial UniqueFactorizationMonoid

namespace LeanPolyABC

variable {k : Type*} [Field k] [DecidableEq k]

variable {α : Type*} [CommMonoidWithZero α] [NormalizationMonoid α] [UniqueFactorizationMonoid α]

theorem prime_dvd_radical_iff {a p : α} (ha : a ≠ 0) (hp : Prime p) :
    p ∣ radical a ↔ p ∣ a := by
  classical
  constructor
  · exact fun h => h.trans <| radical_dvd_self a
  · intro hpa
    rcases exists_mem_normalizedFactors_of_dvd ha hp.irreducible hpa with ⟨q, ⟨hqf, hpq⟩⟩
    rw [hpq.dvd_iff_dvd_left, radical, primeFactors]
    exact Finset.dvd_prod_of_mem id (Multiset.mem_toFinset.mpr hqf)

end LeanPolyABC
end
end
