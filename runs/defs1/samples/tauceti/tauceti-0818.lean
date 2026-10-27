public section

namespace TauCeti

universe uR uA uB

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- If every element is a cycle, the differential and hence the boundaries vanish, so the class
map is a linear equivalence with cohomology. -/
noncomputable def cohomologyEquivOfCyclesEqTop
    (𝒜 : AInfinityAlgebra R A) (hcycles : 𝒜.cycles = ⊤) : A ≃ₗ[R] 𝒜.Cohomology := by
  have hd : 𝒜.differential = 0 := LinearMap.ker_eq_top.mp (𝒜.cycles_def ▸ hcycles)
  have hboundaries : 𝒜.boundariesInCycles = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    apply Subtype.ext
    have hx' := (𝒜.mem_boundariesInCycles).mp hx
    rw [boundaries_def, hd] at hx'
    simpa using hx'
  exact
  (LinearEquiv.ofTop 𝒜.cycles hcycles).symm ≪≫ₗ
    (Submodule.quotEquivOfEqBot _ hboundaries).symm

end AInfinityAlgebra
end TauCeti
end
