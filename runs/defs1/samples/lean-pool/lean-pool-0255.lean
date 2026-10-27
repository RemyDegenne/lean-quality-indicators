@[expose] public section

noncomputable section

open scoped BigOperators

namespace KoetheCounterexample

namespace Linearization

universe u v

variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]

namespace System

/-- The root is `none`; only its row contains `X`. -/
def matrix (S : System k) (a : Fin 3 → R) :
    Matrix (Option S.State) (Option S.State) (Polynomial R) :=
  fun i j => match i, j with
    | none, none => Polynomial.X * edge a S.head
    | none, some j => Polynomial.X * edge a (S.out j)
    | some i, none => edge a (S.input i)
    | some i, some j => edge a (S.step i j)

end System
end Linearization
end KoetheCounterexample
end
end
