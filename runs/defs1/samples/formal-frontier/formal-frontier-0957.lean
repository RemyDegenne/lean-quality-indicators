@[expose] public section

universe v u

namespace CategoryTheory

open Limits

/-- A nested pair of subobjects with an admissible chosen quotient. -/
structure AdmissibleLayer {C : Type u} [Category.{v} C] [Abelian C]
    (P : ObjectProperty C) (B : C) where
  lower : Subobject B
  upper : Subobject B
  lower_le_upper : lower ≤ upper
  admissible : P (cokernel (Subobject.ofLE lower upper lower_le_upper))

end CategoryTheory
end
