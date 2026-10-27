public section

namespace CFSG.Semidihedral.UnitaryDValue

open CFSG.TwoRankLowerBound.Helpers

namespace DValueData

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

theorem x_inv : D.x⁻¹ = D.x := inv_eq_of_mul_eq_one_right D.x_mul_self

end DValueData
end CFSG.Semidihedral.UnitaryDValue
end
