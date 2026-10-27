public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer

open CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G}

namespace ExoticLift

variable {C : ExoticCtx p f K z} (L : ExoticLift C)

theorem B_elem : IsElemAbelian 2 L.B :=
  L.frameData₁.isElemAbelian C.hS.odd C.X.hΩ

end ExoticLift
end CFSG.ClassicalInvolution.NDB
end
