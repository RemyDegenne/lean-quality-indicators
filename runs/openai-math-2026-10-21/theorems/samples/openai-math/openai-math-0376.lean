namespace OAI

namespace Ostmann

open scoped Classical

theorem completedCompensationSets_avoids (A B : Set ℕ) (N hi : ℕ) (Y : ℝ)
    (D : Finset ℕ) (top : ℕ) (cs : List ℕ) (p : ℕ) (hp : p ∈ D) (n : ℕ) :
    p ∉ completedCompensationSets A B N Y hi D top cs n :=
  selectedTailCellPrimes_avoids A B N hi Y D _ p hp

end Ostmann
end OAI
