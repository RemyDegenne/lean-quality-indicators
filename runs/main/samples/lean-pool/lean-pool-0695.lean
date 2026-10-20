@[expose] public section

namespace MooreBound

open Module

namespace DegreeDiameter

variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]

theorem oddEvenRoute {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ∃ route : Fin (n + 1) → Equiv.Perm (Fin n),
      route 0 = 1 ∧
      route (Fin.last n) = π ∧
      ∀ s : Fin n, OrderingStep s (route s.castSucc) (route s.succ) := by
  obtain ⟨route, hzero, hlast, hstep⟩ := OddEvenSorting.oddEvenRoute2 π
  refine ⟨route, ?_, hlast, ?_⟩
  · change route 0 = Equiv.refl _
    exact hzero
  · simpa only [OrderingStep, PrefixSet, OddEvenSorting.OrderingStep2,
      OddEvenSorting.PrefixSet2] using hstep

end DegreeDiameter
end MooreBound
end
