@[expose] public section

variable {R : Type*} [Add R] [Mul R]

namespace RingCon

/--
If `c` is a `RingCon Rᵐᵒᵖ`, then `(a, b) ↦ c b.op a.op` is a `RingCon R`.
-/
def unop (c : RingCon Rᵐᵒᵖ) : RingCon R where
  __ := c.toCon.unop
  mul' h1 h2 := c.toCon.unop.mul h1 h2
  add' h1 h2 := c.add h1 h2

end RingCon
end
