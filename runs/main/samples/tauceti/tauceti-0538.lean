public section

open UpperHalfPlane

open ModularGroup (smul_eq_smul_of_eq_or_eq_neg)

open scoped MatrixGroups Modular

namespace TauCeti

namespace ModularGroup

theorem orbit_mk_I_ne_orbit_mk_ρ :
    (Quotient.mk'' I : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) ≠ Quotient.mk'' ρ :=
  fun h ↦ I_ne_ρ ((orbit_mk_eq_I_iff _root_.ModularGroup.ρ_mem_fd).mp h.symm).symm

end ModularGroup
end TauCeti
end
