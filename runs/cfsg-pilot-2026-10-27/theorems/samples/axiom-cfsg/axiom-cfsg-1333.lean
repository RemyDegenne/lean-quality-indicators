public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace GomiFusion

open Subgroup

open scoped commutatorElement

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b

namespace Setup

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ} {φ : L ≃* antiSp K}
  {TG : Subgroup G} {t : G}

theorem conj_mem_T (hS : Setup L K n φ TG t) {c x : G} (hc : c ∈ centralizer ({t} : Set G))
    (hx : x ∈ TG) : c * x * c⁻¹ ∈ TG :=
  hS.mem_T (conj_mem_centralizer_of_mem_normalizer (hS.cent_le hc)
    (hS.T_le hx)) (mul_mem (mul_mem hc (hS.T_le_C hx)) (inv_mem hc))

end Setup
end GomiFusion
end CFSG.LocalAnalysis.SymplecticFourStandard
end
