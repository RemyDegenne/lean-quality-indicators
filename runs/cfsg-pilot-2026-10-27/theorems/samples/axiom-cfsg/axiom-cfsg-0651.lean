public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix

open scoped commutatorElement Pointwise

namespace SymThreeCentralizerData

variable {D : Type*} [Group D] (S : SymThreeCentralizerData D)

theorem mem_A_of_mem_C_R {x : D} (hx : x ∈ S.C) (hxR : x ∈ S.R) : x ∈ S.A := by
  rcases S.mem_R_iff.1 hxR with h | h
  · exact h
  · exfalso
    apply S.z_not_mem_C
    have := mul_mem hx (inv_mem (S.A_le_C h))
    rwa [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left] at this

end SymThreeCentralizerData
end CFSG.LocalAnalysis.ComponentInitial
end
