namespace P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_hasCharConductor_of_ratio

set_option Elab.async false

p2m_reactivate

section DeskModule00

namespace FLT

namespace AdmissibleRep

p2m_open

section FixedVectors

variable {G : Type*} [Group G]

def fixedVectors (K : Subgroup G) (R : Type*) (M : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] [DistribMulAction G M] [SMulCommClass G R M] : Submodule R M where
  carrier := {v | ∀ k ∈ K, k • v = v}
  zero_mem' := fun k _ => smul_zero k
  add_mem' := by
    intro a b ha hb k hk
    rw [smul_add, ha k hk, hb k hk]
  smul_mem' := by
    intro r v hv k hk
    rw [smul_comm, hv k hk]

end FixedVectors
end AdmissibleRep
end FLT
end DeskModule00
end P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_hasCharConductor_of_ratio
