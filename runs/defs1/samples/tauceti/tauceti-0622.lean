public noncomputable section

open CategoryTheory

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace LayerRestriction

variable {small big : NormalLayer G}

/-- The homomorphism `U'/V → U/V` of Galois groups induced by a restriction. It is injective
(`galHom_injective`), and its image is the subgroup of `U/V` that the intermediate subgroup `U'`
cuts out. -/
def galHom (T : LayerRestriction small big) : small.Gal →* big.Gal :=
  @QuotientGroup.quotientMapSubgroupOfOfLe G _ small.top.toSubgroup small.ground.toSubgroup
    big.top.toSubgroup big.ground.toSubgroup small.normal big.normal
    T.same_top_toSubgroup.le T.ground_toSubgroup_le

end LayerRestriction
end TauCeti.ClassFieldTheory
end
