public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace CentralPrimeInduction

open Subgroup

open NormalLinearInduced (indFamLinear apply_one_of_mem_indFamLinear)

variable {G : Type*} [Group G] {p a : ℕ} {L P E Z : Subgroup G}

namespace IsCentralPrimeInduction

variable (h : IsCentralPrimeInduction p a L P E Z)

include h

theorem disjoint_puncturedAmbient :
    ∀ g ∉ L, (NormalLinearInduced.puncturedAmbient (P.subgroupOf L) : Set G)
      ∩ (fun x => g⁻¹ * x * g) ''
        (NormalLinearInduced.puncturedAmbient (P.subgroupOf L) : Set G) = ∅ := by
  intro g hg
  rw [puncturedAmbient_subgroupOf_eq h.P_le]
  exact h.inter_conj_eq_empty g hg

end IsCentralPrimeInduction
end CentralPrimeInduction
end CFSG.FeitThompson
end
