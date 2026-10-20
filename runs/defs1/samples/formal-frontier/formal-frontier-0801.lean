@[expose] public section

noncomputable section

universe u

namespace Matrix

variable (ι : Type u) [Fintype ι] [LinearOrder ι] (R : Type u) [CommRing R]

/-- The subgroup of native invertible matrices corresponding to Milne's
upper-triangular `T_n` (item 2.9), over any commutative ring. Inversion uses
Mathlib's triangular-inverse theorem, not nonvanishing of the determinant. -/
def upperTriangularSubgroup : Subgroup (GeneralLinearGroup ι R) where
  carrier := {g | (g : Matrix ι ι R).IsUpperTriangular}
  one_mem' := by
    exact Matrix.blockTriangular_one
  mul_mem' := by
    intro left right upperLeft upperRight
    exact upperLeft.mul upperRight
  inv_mem' := by
    intro matrix upper
    have : Invertible (matrix : Matrix ι ι R) := Units.invertible matrix
    change ((matrix⁻¹ : GeneralLinearGroup ι R) : Matrix ι ι R).IsUpperTriangular
    rw [GeneralLinearGroup.coe_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular upper

end Matrix
end
end
