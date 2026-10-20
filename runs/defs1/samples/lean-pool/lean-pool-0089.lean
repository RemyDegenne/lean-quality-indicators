@[expose] public section

namespace VirasoroProject

attribute [local instance 100] LieRing.ofAssociativeRing

section Fock_space_Sugawara_construction

variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]

namespace ChargedFockSpace

/-- A Virasoro module map from the Verma module with `c = 1` and `h = α^2 / 2`
to the charged Fock space of charge `α`. -/
noncomputable def _root_.VirasoroProject.ChargedFockSpace.virasoroVermaToChargedFockSpace (α : 𝕜) :
    VirasoroVerma 𝕜 1 (α^2/2) →ₗ[𝓤 𝕜 (VirasoroAlgebra 𝕜)] ChargedFockSpace 𝕜 α :=
  VirasoroVerma.universalMap 𝕜 _ (hwv := vacuum 𝕜 α) (by simp)
    (by
      rw [sugawaraRepresentation_ιUEA_smul_eq, sugawaraRepresentation_lgen_zero_apply_vacuum]
      rw [algebraMap_virasoro_smul_eq])
    (by
      intro n n_pos
      simpa using sugawaraRepresentation_lgen_pos_apply_vacuum 𝕜 α n_pos)

end ChargedFockSpace
end Fock_space_Sugawara_construction
end VirasoroProject
end
