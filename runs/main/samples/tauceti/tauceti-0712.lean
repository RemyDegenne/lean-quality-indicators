public section

open CliffordAlgebra Module

namespace TauCeti

universe u v

section Odd

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  (P : SpinPolarizationData Q)

variable [NeZero (2 : K)] [FiniteDimensional K V]

variable [IsSepClosed K]

theorem not_forall_map_spinRep_spinPlus_le (l : ℕ) (hV : finrank K V = 2 * l + 1) (hW : P.W ≠ ⊥) :
    ¬ ∀ g : spinGroup Q, (spinPlus Q P).map (spinRep Q P g) ≤ spinPlus Q P :=
  not_forall_map_spinRep_spinPlus_le_of_isIrreducible P (spinRep_isIrreducible_of_odd P l hV) hW

end Odd
end TauCeti
end
