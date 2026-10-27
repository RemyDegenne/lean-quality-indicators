public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS AhatData

section Setup

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L L' : Subgroup G} {n : ℕ} {z a : G}
  (P : StdPair G L L' n z a)

include P in
theorem StdPair.normal_NB : (pairNB L' z a).Normal := ⟨fun x hx b => by
  rw [pairNB_mem_iff] at hx ⊢
  have := mul_mem_centralizer_of_mem_normalizer (P.B_le_normalizer' b.2) hx
  simpa using this⟩

end Setup
end CFSG.OddStandard.Solomon75
end
