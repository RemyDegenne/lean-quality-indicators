public section

namespace TauCeti.freeProP

open Subgroup Submodule

open scoped commutatorElement

universe u

variable {p : ℕ} {X : Type u} {m : ℕ}

section Span

variable [Fact p.Prime] [Finite X] [LinearOrder X]

theorem gradedPow_mem_range_basisModificationDelta_sup_basisModificationTail (hm : 1 ≤ m)
    {ρ : gradedPiece p (freeProP p X) 1} {v : gradedPiece p (freeProP p X) (m + 1)}
    (hv : v ∈ LinearMap.range (basisModificationDelta p X hm ρ) ⊔
      basisModificationTail p X ρ (m + 1)) :
    gradedPow p (freeProP p X) (m + 1) v ∈
      LinearMap.range (basisModificationDelta p X (by omega) ρ) ⊔
        basisModificationTail p X ρ (m + 1 + 1) := by
  rw [basisModificationTail_def] at hv ⊢
  exact gradedPow_mem_range_basisModificationDelta_sup_gradedPowIterSpan hm hv

end Span
end TauCeti.freeProP
end
