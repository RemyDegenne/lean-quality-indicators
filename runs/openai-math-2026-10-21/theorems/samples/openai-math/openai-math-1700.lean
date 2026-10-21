namespace OAI

namespace Ostmann.Supply.CompletionCounting

open Finset

theorem primeFactors_eq_filter {U u : ℕ} (hu : u ∈ Icc 1 U) :
    u.primeFactors = (primesUpTo U).filter (fun p => p ∣ u) := by
  ext p
  constructor
  · intro hp
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr
      ⟨(Nat.prime_of_mem_primeFactors hp).two_le,
        (Nat.le_of_mem_primeFactors hp).trans (mem_Icc.mp hu).2⟩,
        Nat.prime_of_mem_primeFactors hp⟩, Nat.dvd_of_mem_primeFactors hp⟩
  · intro hp
    obtain ⟨hp, hpu⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(mem_filter.mp hp).2, hpu,
      by have := (mem_Icc.mp hu).1; omega⟩

end Ostmann.Supply.CompletionCounting
end OAI
