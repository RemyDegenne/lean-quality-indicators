@[expose] public section

open CategoryTheory Filter

open scoped Topology

universe u

attribute [instance] FiniteGroupPresentation.smallCategory FiniteGroupPresentation.cofiltered

theorem finiteGroupPresentation_iff_compact_totallyDisconnected (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] :
    Nonempty (FiniteGroupPresentation G) ↔
      CompactSpace G ∧ TotallyDisconnectedSpace G := by
  constructor
  · rintro ⟨P⟩
    exact ⟨Homeomorph.compactSpace P.equiv.symm.toHomeomorph,
      Homeomorph.totallyDisconnectedSpace P.equiv.symm.toHomeomorph⟩
  · rintro ⟨hcompact, hdisconnected⟩
    let : CompactSpace G := hcompact
    let : TotallyDisconnectedSpace G := hdisconnected
    exact ⟨FiniteGroupPresentation.ofProfiniteGrp (ProfiniteGrp.of G)⟩

end
