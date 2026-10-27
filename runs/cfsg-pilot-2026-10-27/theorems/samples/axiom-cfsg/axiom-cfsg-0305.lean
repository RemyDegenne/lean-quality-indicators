public section

open scoped commutatorElement

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6X.End3
  CFSG.CGT.PushingUpLit.BHS6

variable {V : Type} [CommGroup V]

section Cover

variable {Γ Q : Type*} [Group Γ] [Group Q]

theorem commutatorElement_mul_central_left {a b z : Γ} (hz : z ∈ Subgroup.center Γ) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.mp hz b
  calc ⁅a * z, b⁆ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by simp only [commutatorElement_def]; group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [h]
    _ = ⁅a, b⁆ := by simp only [commutatorElement_def]; group

end Cover
end CFSG.CGT.PushingUpLit.CGT6X.End4
end
