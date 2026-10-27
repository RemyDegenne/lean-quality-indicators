public section

namespace TauCeti.ConstructionA

open Matrix

variable (m : ℕ) [NeZero m] (ι : Type*) [Fintype ι]

/-- **The dual carrier of the zero-code lattice is the integer coordinate lattice**, presented as
a `ℤ`-linear equivalence with `ℤ^ι` given by the coordinatewise integer cast. -/
noncomputable def dualCarrierIntEquiv : (ι → ℤ) ≃ₗ[ℤ] (zeroLattice m ι).dualCarrier :=
  LinearEquiv.ofBijective
    (((Int.castAddHom ℚ).toIntLinearMap.compLeft ι).codRestrict _
      (intCastPi_mem_dualCarrier m ι))
    ⟨fun _ _ h ↦ (Function.Injective.piMap fun _ ↦ Int.cast_injective)
        (congrArg Subtype.val h), fun x ↦ by
      obtain ⟨z, hz⟩ := (mem_zeroLattice_dualCarrier_iff m ι).mp x.2
      exact ⟨z, Subtype.ext hz⟩⟩

end TauCeti.ConstructionA
end
