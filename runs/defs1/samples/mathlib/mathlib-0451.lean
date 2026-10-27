@[expose] public section

universe u u' v

namespace QPF

variable {F : Type u → Type u} [q : QPF F]

open Functor (Liftp Liftr supp)

open Set

/-- A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range. -/
def IsUniform : Prop :=
  ∀ ⦃α : Type u⦄ (a a' : q.P.A) (f : q.P.B a → α) (f' : q.P.B a' → α),
    abs (.mk a f) = abs (.mk a' f') → f '' univ = f' '' univ

end QPF
end
