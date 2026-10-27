public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14 QuadraticMap

open CFSG.LargeExtraspecial.S14.SMK (Inputs10)

open CFSG.GF2Type.SmithTypeE.LMod

open CFSG.LargeExtraspecial.SMod20 (V exists_linear_of_gram)

open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G] {S : Setting G}

section Phi

theorem planeHom_of_mem (ψ : Mbar0 S ≃* T6) (m : Mbar0 S) (i : Fin 1395) :
    planeHom S ψ (m : S.Mbar) i = ψ m • i := by
  rw [planeHom_eq_iff, piM_of_mem]
  exact image_wPlane_smul (ψ m) i

end Phi
end CFSG.GF2Type.SmithTypeE.L6
end
