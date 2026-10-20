namespace P2MW.S_LocalNewvector_PSCarrier_finrank_inf_fixedSubmodule_padicK1_of_stable

set_option Elab.async false

p2m_reactivate

section DeskModule00

p2m_reactivate

p2m_reactivate

open FLT.SmoothVectors FLT.AdmissibleRep

namespace FLT

namespace EKAverage

p2m_open

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Bundled

variable (F : Type*) [Field F] [CharZero F] {G : Type*} [Group G] {M : Type*} [AddCommGroup M]
  [Module F M] [DistribMulAction G M] [SMulCommClass G F M]

variable (K : Subgroup G)

noncomputable def ekAverageHom (hfin : ∀ v : M, Finite (↥K ⧸ MulAction.stabilizer K v)) :
    M →ₗ[F] M where
  toFun v := ekAverage F K v
  map_add' v w := by
    haveI := hfin v
    haveI := hfin w
    exact ekAverage_add
  map_smul' c v := by
    haveI := hfin v
    simpa using ekAverage_const_smul (F := F) c v

end Bundled
end EKAverage
end FLT
end DeskModule00
end P2MW.S_LocalNewvector_PSCarrier_finrank_inf_fixedSubmodule_padicK1_of_stable
