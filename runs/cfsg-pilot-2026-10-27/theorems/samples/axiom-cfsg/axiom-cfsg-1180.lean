public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair

open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP

open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

section L33c

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

theorem A_le_C₀ (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) (h3 : SPL3X D) :
    D.A ≤ D.C₀ := fun a ha =>
  (mem_C₀ D).mpr (fun y hy => (hc.AI_comm a ha y (Y₀_le_I D hs hc h3 hy)).symm)

end L33c
end CFSG.GH74.GLS.SP.Local
end
