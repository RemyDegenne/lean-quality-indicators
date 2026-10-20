public section

namespace Algebra.GrothendieckAddGroup.GradedStabilization

open Algebra Algebra.GrothendieckAddGroup

universe uM uA

variable {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A]

/-- Stabilization by the missing natural number of copies of `u`. -/
@[expose] def transition (d : M →+ A) (u : M) (n k : ℕ) (h : n ≤ k) :
    TypeCat.Fun (degreeFiber d u n) (degreeFiber d u k) :=
  ⟨fun m => ⟨m.1 + (k - n) • u, by
    rw [map_add, map_nsmul, m.2, ← add_nsmul]
    congr 1
    omega⟩⟩

end Algebra.GrothendieckAddGroup.GradedStabilization
end
