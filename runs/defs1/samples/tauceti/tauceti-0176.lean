public noncomputable section

open CategoryTheory Representation

namespace TauCeti.ClassFieldTheory

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- A **finite normal layer** `V ◁ U` of open subgroups of `G`. In field notation this is the
finite Galois layer `K/F` inside the extension `G` cuts out, with `U = G_F` the ground subgroup and
`V = G_K` the top subgroup. -/
@[ext]
structure NormalLayer (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] where
  /-- the ground subgroup `U`, cutting out the base field of the layer -/
  ground : OpenSubgroup G
  /-- the top subgroup `V`, cutting out the top field of the layer -/
  top : OpenSubgroup G
  /-- the layer runs upwards: `V ≤ U` -/
  top_le_ground : top ≤ ground
  /-- `V` is normal in `U`, so that the layer is Galois -/
  normal : (top.toSubgroup.subgroupOf ground.toSubgroup).Normal

end TauCeti.ClassFieldTheory
end
