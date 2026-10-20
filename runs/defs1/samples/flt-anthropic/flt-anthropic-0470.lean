namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell

namespace CubicInduction

namespace JacquetVanishing

p2m_open

p2m_open

section GL2

variable {A : Type*} [CommRing A]

def repMid (e : A) : GL (Fin 2) A where
  val := !![0, 1; 1, e]
  inv := !![-e, 1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end GL2
end JacquetVanishing
end CubicInduction
end LanglandsTunnell
end P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3
