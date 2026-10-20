namespace P2MW.S_ModularCurve_PDPairing_pairZFun_heckeT0_comm

set_option autoImplicit false

open scoped MatrixGroups

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace ModularCurve

namespace PDPairing

namespace TD

p2m_open

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Rows

open MulAction

variable {R : Type*} [CommRing R]

section PlusMinus

open Matrix Matrix.SpecialLinearGroup ModularGroup

scoped instance pm_finiteIndex (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] : (pm Φ).FiniteIndex :=
  Subgroup.finiteIndex_of_le (le_pm Φ)

theorem trace_intertwine (a V V'' : Matrix (Fin 2) (Fin 2) ℤ) (ha : a.det ≠ 0) (h : a * V = V'' * a) :
    V''.trace = V.trace := by
  have e := fun i j => congrFun (congrFun h i) j
  have h00 := e 0 0
  have h01 := e 0 1
  have h10 := e 1 0
  have h11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  rw [Matrix.det_fin_two] at ha
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  have key : (a 0 0 * a 1 1 - a 0 1 * a 1 0) * ((V'' 0 0 + V'' 1 1) - (V 0 0 + V 1 1)) = 0 := by
    linear_combination (-(a 1 1)) * h00 + (a 1 0) * h01 + (a 0 1) * h10 + (-(a 0 0)) * h11
  have := (mul_eq_zero.mp key).resolve_left ha
  linear_combination this

end PlusMinus
end Rows
end TD
end PDPairing
end ModularCurve
end P2MW.S_ModularCurve_PDPairing_pairZFun_heckeT0_comm
