namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_le_isOrder_forall_exists_pow_smul_mem_and_act_and_forall_exists_generalLinearGroup_and_exists_isMaximalOrder_inf_eq_of_isOrder_act_of_conj_of_injective

attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup

set_option autoImplicit false

p2m_open

open scoped Quaternion MatrixGroups

namespace CerednikDrinfeld

namespace QM

namespace FakeEllipticCurve

namespace EndIsoExport

p2m_open

section Conj

variable {a₁ b₁ : ℚ}

def cj (u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] ℍ[ℚ, a₁, b₁] where
  toFun z := ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * z * ((u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])
  map_one' := by simp
  map_mul' x y := by
    calc ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * (x * y) * (u : ℍ[ℚ, a₁, b₁])
        = (u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) * x * (((u : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
            ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) * y * (u : ℍ[ℚ, a₁, b₁]) := by
          rw [Units.mul_inv]; simp [mul_assoc]
      _ = (u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) * x * (u : ℍ[ℚ, a₁, b₁]) *
            (((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * y * (u : ℍ[ℚ, a₁, b₁])) := by
          simp [mul_assoc]
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]
  commutes' c := by
    show ((u⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * algebraMap ℚ ℍ[ℚ, a₁, b₁] c * (u : ℍ[ℚ, a₁, b₁]) =
      algebraMap ℚ ℍ[ℚ, a₁, b₁] c
    rw [mul_assoc, Algebra.commutes, ← mul_assoc, Units.inv_mul, one_mul]

end Conj
end EndIsoExport
end FakeEllipticCurve
end QM
end CerednikDrinfeld
end P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_le_isOrder_forall_exists_pow_smul_mem_and_act_and_forall_exists_generalLinearGroup_and_exists_isMaximalOrder_inf_eq_of_isOrder_act_of_conj_of_injective
