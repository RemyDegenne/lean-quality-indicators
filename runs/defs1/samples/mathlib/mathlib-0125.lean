@[expose] public section

universe u v

open ULift CategoryTheory MulOpposite

namespace Traversable

open Monoid Functor

section Defs

variable {α β : Type u} {t : Type u → Type u} [Traversable t]

def foldMap {α ω} [One ω] [Mul ω] (f : α → ω) : t α → ω :=
  traverse (Const.mk' ∘ f)

end Defs
end Traversable
end
