public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.CaseD

open CFSG.LargeExtraspecial Subgroup

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

theorem map_clSub_eq_of_fix {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (m : S.M)
    (hm : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹)) :
    (S.clSub (S.QG ⊓ S.Qa g)).map
        (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
      S.clSub (S.QG ⊓ S.Qa g) := by
  rw [← clSub_inf_Qa_mul S m g]
  exact congrArg S.clSub (QG_inf_Qa_mul_eq_of_fix S haQ hne m hm)

end CFSG.GF2Type.Smith1979W3.CaseD
end
