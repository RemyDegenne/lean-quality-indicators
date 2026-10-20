@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

open scoped MonObj

universe v u

variable (D : Type u)

variable {D}

/-- **Locally mixed**: after base change to some nonzero
commutative algebra, the object becomes a sum of copies of the
unit and the line. -/
def OddLine.LocallyMixed
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (X : D) : Prop :=
  ∃ (p q : ℕ) (A : D) (_ : MonObj A) (_ : IsCommMonObj A),
    η[A] ≠ 0 ∧
    Nonempty (freeMod A X ≅ freeMod A (L.mix p q))

end RS
end
