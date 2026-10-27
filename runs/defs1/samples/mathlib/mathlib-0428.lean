@[expose] public section

universe u v

namespace MvQPF

open TypeVec

open MvFunctor (LiftP LiftR)

open MvFunctor

variable {n : ℕ} {F : TypeVec.{u} (n + 1) → Type u} [q : MvQPF F]

attribute [local instance] wSetoid

/-- `Fix F` is a functor -/
def Fix.map {α β : TypeVec n} (g : α ⟹ β) : Fix F α → Fix F β :=
  Quotient.lift (fun x : q.P.W α => ⟦q.P.wMap g x⟧) fun _a _b h => Quot.sound (wEquiv_map _ _ _ h)

end MvQPF
end
