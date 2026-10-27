public section

namespace CFSG.StandardType.TestLin

open Matrix

variable {r : ℕ}

theorem extFrameFun2_of_not_lt (τ : Equiv.Perm (Fin r)) {i : Fin (r + 2)}
    (h : ¬ i.val < r) : extFrameFun2 τ i = i := by
  simp [extFrameFun2, h]

end CFSG.StandardType.TestLin
end
