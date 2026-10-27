@[expose] public section

universe w v u

namespace CategoryTheory

namespace Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

namespace Adj

section

variable (a b : B)

/--
Given two objects `a` and `b` in a bicategory,
this is the type of adjunctions between `a` and `b`.
-/
structure Hom where
  /-- the left adjoint -/
  {l : a ⟶ b}
  /-- the right adjoint -/
  {r : b ⟶ a}
  /-- the adjunction -/
  adj : l ⊣ r

end
end Adj
end Bicategory
end CategoryTheory
end
