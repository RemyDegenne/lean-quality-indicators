public section

namespace CFSG.OddStandard.AltStdSmall4.G2

open Subgroup Matrix AltStdCycTwo

open scoped Pointwise

section Lfree

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G}

theorem z_not_mem_Lfree (c : Config G L Q n θ z) : z ∉ Lfree L z := fun hz =>
  N0.z_not_mem_L c (mem_L_of_two_pow c hz (j := 1) (by rw [pow_one, sq, z_mul_self c]))

end Lfree
end CFSG.OddStandard.AltStdSmall4.G2
end
