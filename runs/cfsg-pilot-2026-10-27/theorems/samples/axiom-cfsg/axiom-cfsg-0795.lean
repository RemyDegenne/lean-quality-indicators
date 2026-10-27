public section

namespace CFSG.Monster.B.TwoA.Unitary.LinThree

open CFSG.Fischer CFSG.Monster.B.Classical.Plane CFSG.Monster.B.Classical.ThreePlane
  CFSG.LinearGroups CFSG.Monster.B.TwoA

open CFSG.Monster.Code (AutPerm)

open scoped LinearAlgebra.Projectivization MatrixGroups Matrix

attribute [local instance] restAction

theorem genP_mem_P₂L_iff
    (k : Fin 6) : genP k ∈ P₂L ↔ genFrob k = 0 := by
  rw [mem_P₂L_iff, psi_genP]
  change Multiplicative.ofAdd (genFrob k) = 1 ↔ _
  exact ofAdd_eq_one

end CFSG.Monster.B.TwoA.Unitary.LinThree
end
