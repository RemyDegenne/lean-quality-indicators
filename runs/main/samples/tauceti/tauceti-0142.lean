public section

open Subgroup

open scoped commutatorElement

namespace TauCeti

universe u v w

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

@[simp]
theorem gradedCast_neg {j k : ℕ} (h : j = k) (x : gradedPiece p G j) :
    gradedCast p G h (-x) = -gradedCast p G h x := by
  subst h; rfl

end TauCeti
end
