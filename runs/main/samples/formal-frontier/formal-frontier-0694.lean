public section

namespace Algebra.GrothendieckAddGroup.GradedStabilization

open Algebra Algebra.GrothendieckAddGroup

universe uM uA

variable {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A]

theorem normalizedAt_transition (d : M →+ A) (u : M) (n k : ℕ) (h : n ≤ k)
    (m : degreeFiber d u n) :
    normalizedAt d u n m = normalizedAt d u k (transition d u n k h m) := by
  apply Subtype.ext
  change of m.1 - n • of u = of (m.1 + (k - n) • u) - k • of u
  rw [map_add, map_nsmul]
  have hk : k • of u = n • of u + (k - n) • of u := by
    rw [← add_nsmul]
    congr 1
    omega
  rw [hk]
  abel

end Algebra.GrothendieckAddGroup.GradedStabilization
end
