public noncomputable section

open CategoryTheory Representation

namespace TauCeti.ClassFieldTheory

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

namespace NormalLayer

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (L : NormalLayer G)

/-- The **degree** `[U : V]` of a normal layer, the index of the top subgroup in the ground
subgroup. -/
def degree : ℕ := L.relativeTop.index

end NormalLayer
end TauCeti.ClassFieldTheory
end
