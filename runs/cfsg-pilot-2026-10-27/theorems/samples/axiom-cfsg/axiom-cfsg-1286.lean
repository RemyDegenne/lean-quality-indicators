public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix

open scoped commutatorElement Pointwise

namespace SymThreeCosetData

variable {D : Type*} [Group D] (S : SymThreeCosetData D)

theorem ρ_mem_F (g : GL (Fin 3) (ZMod 2)) {d : D} (hd : d ∈ S.F) : S.ρ g d ∈ S.F := by
  rw [mem_F, ν_ρ, symThreeDiag_coe_congr, S.mem_F.1 hd, mulVec_zero]

end SymThreeCosetData
end CFSG.LocalAnalysis.ComponentInitial
end
