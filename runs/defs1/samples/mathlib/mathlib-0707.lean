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

/-- does `abs` preserve `liftp`? -/
def LiftPPreservation : Prop :=
  ∀ ⦃α : TypeVec n⦄ (p : ∀ ⦃i⦄, α i → Prop) (x : q.P α), LiftP p (abs x) ↔ LiftP p x

end MvQPF
end
