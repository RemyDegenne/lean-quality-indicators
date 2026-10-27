public section

namespace CFSG.Quasithin.SteinbergBS

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.ComponentClassification CFSG.ABGLocalTools

open scoped MatrixGroups Pointwise

section Coordinates

variable {F : Type} [Field F]

theorem proj_injOn_unitriangular {u v : SL(3, F)} (hu : u ∈ LinearFlag.unitriangular 3 F)
    (hv : v ∈ LinearFlag.unitriangular 3 F) (h : proj 3 F u = proj 3 F v) : u = v := by
  have h3 : u⁻¹ * v ∈ LinearFlag.unitriangular 3 F ⊓ scalars 3 F :=
    Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hu) hv, proj_eq_proj_iff.1 h⟩
  rw [unitriangular_inf_scalars, mem_bot] at h3
  exact inv_mul_eq_one.1 h3

end Coordinates
end CFSG.Quasithin.SteinbergBS
end
