public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace Type300

section

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

theorem t_b (n : ℕ) :
    (action n).φt Torus.b = (-4 : ℤ) • Torus.c + (-2 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  refine (matAct_gen_of tM (compat_t n) 2 (-4) (-2) (-1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

end
end Type300
end CFSG.CGT.Stroth77
end
