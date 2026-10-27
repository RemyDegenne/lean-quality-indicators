public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB TableBSymp

namespace NbrSp

section Coord

variable {p m : ℕ}

theorem mul_inv_update_eq (f : Fin m → Multiplicative (ZMod p)) (i : Fin m) :
    f * (Function.update f i (f i)⁻¹)⁻¹ = Pi.mulSingle i (f i ^ 2) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [sq]
  · simp [Function.update_of_ne hj, Pi.mulSingle_eq_of_ne hj]

end Coord
end NbrSp
end CFSG.StandardType
end
