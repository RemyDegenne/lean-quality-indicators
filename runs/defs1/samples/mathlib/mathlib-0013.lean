@[expose] public section

universe u v w

namespace Functor

/-- `Functor.Comp` is a wrapper around `Function.Comp` for types.
It prevents Lean's type class resolution mechanism from trying
a `Functor (Comp F id)` when `Functor F` would do. -/
def Comp (F : Type u → Type w) (G : Type v → Type u) (α : Type v) : Type w :=
  F <| G α

end Functor
end
