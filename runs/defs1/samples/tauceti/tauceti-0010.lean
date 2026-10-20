public section

namespace TauCeti

/-- The group of continuous outer automorphisms of `G`: continuous automorphisms modulo the inner
ones. -/
abbrev ContinuousOut (G : Type*) [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] :=
  ContinuousAut G ⧸ (ContinuousAut.conj : G →* ContinuousAut G).range

end TauCeti
end
