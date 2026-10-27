namespace P2MW.S_ModularCurve_coe_diamondAutHBar_eq_coe_diamondAutHBar_div_of_coe_eq

set_option autoImplicit false

open scoped MatrixGroups ModularForm

p2m_open

namespace ModularCurve

namespace DResBarBody

p2m_open

def toRingAutHom {F : Type*} [Field F] {A : Algebra ℚ F} {G : Type*} [Group G] (ρ : G →* (F ≃ₐ[ℚ] F)) : G →* RingAut F where
  toFun g := (ρ g).toRingEquiv
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [AlgEquiv.mul_apply, RingAut.mul_apply]

end DResBarBody
end ModularCurve
end P2MW.S_ModularCurve_coe_diamondAutHBar_eq_coe_diamondAutHBar_div_of_coe_eq
