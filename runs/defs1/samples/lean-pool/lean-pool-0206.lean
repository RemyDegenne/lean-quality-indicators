@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {A : Type u}

/-- **The odd line of the doubling**: the unit in odd degree. -/
noncomputable def doubledOddLine
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [MonoidalPreadditive A] [HasBinaryBiproducts A]
    [HasZeroObject A] : OddLine (Doubled A) where
  obj := Doubled.oddUnit
  sq := Doubled.oddUnitSq
  braid_neg := Doubled.braiding_oddUnit

end RS
end
