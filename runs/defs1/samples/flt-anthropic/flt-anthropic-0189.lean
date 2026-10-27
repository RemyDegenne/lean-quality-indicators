namespace P2MW.S_Matrix_ProjGenLinGroup_exists_torsionFree_normal_subgroup_finiteIndex_of_fg_charZero

set_option autoImplicit false

open scoped MatrixGroups

namespace SelbergPGL

variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]

noncomputable def adMat (g : GL n K) : Matrix (n × n) (n × n) K :=
  LinearMap.toMatrix (Matrix.stdBasis K n n) (Matrix.stdBasis K n n) (adLin g)

end SelbergPGL
end P2MW.S_Matrix_ProjGenLinGroup_exists_torsionFree_normal_subgroup_finiteIndex_of_fg_charZero
