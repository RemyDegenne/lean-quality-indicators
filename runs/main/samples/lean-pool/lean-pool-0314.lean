@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace Moise

namespace PolygonalCircle

theorem regions_eq_of_carrier_eq {J J' : PolygonalCircle}
    (hcarrier : J.carrier = J'.carrier) :
    J.interiorRegion = J'.interiorRegion ∧ J.exteriorRegion = J'.exteriorRegion := by
  have hsplitJ' : J'.exteriorRegion ⊆ J.interiorRegion ∪ J.exteriorRegion := by
    intro p hp
    have hpCompl : p ∈ J'.carrierᶜ := by
      rw [← J'.interior_union_exterior]
      exact Or.inr hp
    have hpCompl' : p ∈ J.carrierᶜ := by rwa [hcarrier]
    rwa [← J.interior_union_exterior] at hpCompl'
  have hmeetExterior : (J'.exteriorRegion ∩ J.exteriorRegion).Nonempty := by
    by_contra h
    have hsubsetInterior : J'.exteriorRegion ⊆ J.interiorRegion := by
      intro p hp
      rcases hsplitJ' hp with hpInt | hpExt
      · exact hpInt
      · exact False.elim <| h ⟨p, hp, hpExt⟩
    exact J'.not_isBounded_exteriorRegion
      (J.isBounded_interiorRegion.subset hsubsetInterior)
  have hExteriorSub : J'.exteriorRegion ⊆ J.exteriorRegion :=
    J'.isConnected_exteriorRegion.isPreconnected.subset_right_of_subset_union
      J.isOpen_interiorRegion J.isOpen_exteriorRegion J.disjoint_interior_exterior
      hsplitJ' hmeetExterior
  have hsplitJ : J.exteriorRegion ⊆ J'.interiorRegion ∪ J'.exteriorRegion := by
    intro p hp
    have hpCompl : p ∈ J.carrierᶜ := by
      rw [← J.interior_union_exterior]
      exact Or.inr hp
    have hpCompl' : p ∈ J'.carrierᶜ := by rwa [← hcarrier]
    rwa [← J'.interior_union_exterior] at hpCompl'
  have hmeetExterior' : (J.exteriorRegion ∩ J'.exteriorRegion).Nonempty := by
    obtain ⟨p, hpJ', hpJ⟩ := hmeetExterior
    exact ⟨p, hpJ, hpJ'⟩
  have hExteriorSub' : J.exteriorRegion ⊆ J'.exteriorRegion :=
    J.isConnected_exteriorRegion.isPreconnected.subset_right_of_subset_union
      J'.isOpen_interiorRegion J'.isOpen_exteriorRegion J'.disjoint_interior_exterior
      hsplitJ hmeetExterior'
  have hExterior : J.exteriorRegion = J'.exteriorRegion :=
    Set.Subset.antisymm hExteriorSub' hExteriorSub
  refine ⟨?_, hExterior⟩
  have hcomplements : J.interiorRegion ∪ J.exteriorRegion =
      J'.interiorRegion ∪ J'.exteriorRegion := by
    rw [J.interior_union_exterior, J'.interior_union_exterior, hcarrier]
  apply Set.Subset.antisymm
  · intro p hp
    have hpUnion : p ∈ J'.interiorRegion ∪ J'.exteriorRegion := by
      rw [← hcomplements]
      exact Or.inl hp
    rcases hpUnion with hpInt | hpExt
    · exact hpInt
    · exact False.elim <| Set.disjoint_left.mp J.disjoint_interior_exterior
        hp (hExterior ▸ hpExt)
  · intro p hp
    have hpUnion : p ∈ J.interiorRegion ∪ J.exteriorRegion := by
      rw [hcomplements]
      exact Or.inl hp
    rcases hpUnion with hpInt | hpExt
    · exact hpInt
    · exact False.elim <| Set.disjoint_left.mp J'.disjoint_interior_exterior
        hp (hExterior ▸ hpExt)

end PolygonalCircle
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
