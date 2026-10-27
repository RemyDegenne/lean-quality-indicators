public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3T8.AF

open scoped commutatorElement

section Helpers

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem layerImg3_conj_Y {z : G} {K : Subgroup G} (y : ↥(Q3NL.exactLayer3 Ω z)) :
    Layer.layerImg3 Ω z (conjSub (y : G) K) =
      conjSub (layerHom Ω z y) (Layer.layerImg3 Ω z K) := by
  have hyc : (y : G) ∈ T8.cenZ z := Layer.exactLayer3_le_cenZ Ω z y.2
  unfold Layer.layerImg3
  rw [← Layer.exactCore3_conj_cen hyc, ← conjSub_subgroupOf, AscQuot.map_conjSub]

end Helpers
end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
end
