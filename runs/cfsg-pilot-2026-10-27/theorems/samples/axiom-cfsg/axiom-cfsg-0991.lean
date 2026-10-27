public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer

open scoped commutatorElement

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

theorem secIsQuasisimple_K : IsQuasisimple (↥h.K ⧸ pPrimeCore 2 ↥h.K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 h.K h.W h.isPComponent_K.1).mp
    h.isPComponent_K.2).2.2

end Hyp52
end CFSG.ComponentClassification.GSThmB
end
