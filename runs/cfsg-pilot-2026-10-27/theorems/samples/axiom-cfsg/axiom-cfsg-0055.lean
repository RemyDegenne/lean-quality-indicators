public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

open CFSG.LieType.Ree.LargeReeCover (torusPair)

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

theorem R_le_RA1 : h.R ≤ d.RA1 := le_sup_left

end LevelOneData
end CFSG.LocalAnalysis.EvenBN.TwoF4
end
