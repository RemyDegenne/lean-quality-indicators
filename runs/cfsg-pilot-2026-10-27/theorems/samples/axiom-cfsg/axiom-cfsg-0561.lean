public section

namespace CFSG.Quasithin.MS93.S51

open Matrix MSP CFSG.LocalAnalysis.ComponentInitial

open scoped LinearAlgebra.Projectivization

variable {F : Type} [Field F]

variable [CharP F 2]

theorem form_e₂_xBar : form F (e₂ F) (mat (xBar F) *ᵥ e₂ F) ≠ 0 := by
  rw [xBar_mulVec_e₂, form_e₂]
  simp

end CFSG.Quasithin.MS93.S51
end
