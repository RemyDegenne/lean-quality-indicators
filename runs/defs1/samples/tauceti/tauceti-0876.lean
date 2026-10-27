public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Subgroup
  Subgroup.Commensurable HeckeRing.GLn

open scoped Pointwise MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-- The image of `Γ₀(N)` in `GL₂(ℚ)`. -/
noncomputable def Gamma0Image : Subgroup (GL (Fin 2) ℚ) :=
  (Gamma0 N).map (mapGL ℚ)

end HeckeRing.GL2
end
