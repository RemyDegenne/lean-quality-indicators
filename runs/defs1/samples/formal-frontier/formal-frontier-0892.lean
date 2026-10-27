set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uX uY uR

variable {X : Type uX} {Y : Type uY} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] {R : Type uR} [Ring R]

/-- Switch the rectangular factors of a unit represented by `1 + A * B`. -/
def rectangularUnitSwitch (A : Matrix X Y R) (B : Matrix Y X R)
    (g : GL X R) (hg : (g : Matrix X X R) = 1 + A * B) : GL Y R := by
  letI : Invertible (1 + A * B : Matrix X X R) := hg ▸ g.invertible
  letI : Invertible (1 : Matrix X X R) := invertibleOne
  letI : Invertible (1 : Matrix Y Y R) := invertibleOne
  letI : Invertible (⅟(1 : Matrix X X R) + A * ⅟(1 : Matrix Y Y R) * B) := by
    simpa only [invOf_one, Matrix.one_mul, Matrix.mul_one] using
      (inferInstance : Invertible (1 + A * B : Matrix X X R))
  letI : Invertible (1 + B * A : Matrix Y Y R) := by
    simpa only [Matrix.mul_one] using
      (Matrix.invertibleAddMulMul (1 : Matrix Y Y R) B (1 : Matrix X X R) A)
  exact unitOfInvertible (1 + B * A)

end Matrix.GeneralLinearGroup
end
