public section

open scoped Matrix Quaternion

namespace Quaternion

/-- **The unit quaternions are the special unitary group of degree two**: the group `Sp(1)` of unit
Hamilton quaternions is `SU(2)`, by `Quaternion.toComplexMatrix`. -/
noncomputable def unitaryEquivSpecialUnitaryGroup :
    unitary ℍ[ℝ] ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  MulEquiv.ofBijective unitaryToSpecialUnitaryGroup
    ⟨fun p q hpq => Subtype.ext (toComplexMatrix_injective (congrArg Subtype.val hpq)),
      fun M => by
        obtain ⟨q, hq, hqM⟩ := exists_eq_toComplexMatrix_of_mem_specialUnitaryGroup M.2
        exact ⟨⟨q, hq⟩, Subtype.ext hqM⟩⟩

end Quaternion
end
