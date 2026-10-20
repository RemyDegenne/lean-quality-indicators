@[expose] public section

open Finset

open Fintype (card)

namespace SimpleGraph

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} {K K' : Type*}

namespace EdgeLabeling

variable {C : EdgeLabeling G K}

@[simp]
theorem get_pullback {f : G' ↪g G} (x y) (h : G'.Adj x y) :
    (C.pullback f).get x y h = C.get (f x) (f y) (by simpa) :=
  rfl

end EdgeLabeling
end SimpleGraph
end
