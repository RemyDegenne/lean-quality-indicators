public section

open Finset

namespace TauCeti

variable {κ V : Type*} [Fintype V] [DecidableEq V]

namespace Polyad3

variable {S : PairSkeleton3 κ V}

/-- The pair graph of a polyad on roles zero and two. -/
noncomputable def pairSupport₀₂ (P : Polyad3 S) :
    Finset {p : V × V // p.1 ≠ p.2} := by
  classical
  exact univ.filter fun p ↦
    p.1.1 ∈ P.c₀ ∧ p.1.2 ∈ P.c₂ ∧ S.pairColors.color p = P.color₀₂

end Polyad3
end TauCeti
end
