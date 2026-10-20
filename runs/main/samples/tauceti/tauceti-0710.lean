public section

namespace TauCeti

open Finset

namespace NumericalType

universe u

variable (T : NumericalType.{u})

variable {T}

namespace IsSelfIntersectionMinusTwoChain

variable {t : ℕ} {c : ℕ → T.Component}

lemma reverse (hc : T.IsSelfIntersectionMinusTwoChain t c) :
    T.IsSelfIntersectionMinusTwoChain t fun i ↦ c (t - 1 - i) where
  injOn i hi j hj h := by
    have := hc.injOn (t - 1 - i) (by omega) (t - 1 - j) (by omega) h
    omega
  intersection_self i hi := hc.intersection_self (t - 1 - i) (by omega)
  intersection_succ_pos i hi := by
    rw [T.intersection_comm]
    exact hc.intersection_pos (by omega) (by omega)

end IsSelfIntersectionMinusTwoChain
end NumericalType
end TauCeti
end
