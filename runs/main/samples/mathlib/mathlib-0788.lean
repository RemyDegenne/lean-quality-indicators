@[expose] public section

set_option linter.style.longLine false in
/-!
## Reference

[Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

universe u

open MvFunctor

namespace MvQPF

variable {n : ℕ} {F : TypeVec.{u} n → Type*} [q : MvQPF F]

open MvFunctor (LiftP LiftR)

open Set

set_option backward.isDefEq.respectTransparency false in
theorem suppPreservation_iff_isUniform : q.SuppPreservation ↔ q.IsUniform := by
  constructor
  · intro h α a a' f f' h' i
    rw [← MvPFunctor.supp_eq, ← MvPFunctor.supp_eq, ← h, h', h]
  · rintro h α ⟨a, f⟩
    ext
    rwa [supp_eq_of_isUniform, MvPFunctor.supp_eq]

end MvQPF
end
