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

/-- A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range. -/
def IsUniform : Prop :=
  ∀ ⦃α : TypeVec n⦄ (a a' : q.P.A) (f : q.P.B a ⟹ α) (f' : q.P.B a' ⟹ α),
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ → ∀ i, f i '' univ = f' i '' univ

end MvQPF
end
