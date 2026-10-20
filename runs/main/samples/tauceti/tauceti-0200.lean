public section

open Module Matrix

namespace TauCeti.IntegralLattice

@[simp] theorem binaryDeterminant23_determinant : binaryDeterminant23.determinant = 23 := by
  rw [determinant_eq_gramDet _ binaryDeterminant23Basis, gramDet_def,
    gramMatrix_binaryDeterminant23Basis]
  norm_num [Matrix.det_fin_two]

end TauCeti.IntegralLattice
end
