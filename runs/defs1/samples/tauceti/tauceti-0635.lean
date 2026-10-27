public section

noncomputable section

namespace TauCeti

open scoped Topology Topology.Homotopy

universe u

variable {S : Type u} (R : Set (FreeGroup S))

/-- The **cellular classifying space** of the presentation `⟨S | R⟩`: the presentation complex
`TauCeti.PresentationComplex R` with cells of dimension at least `3` attached to kill all of its
higher homotopy groups at its vertex. It is a `K(PresentedGroup R, 1)`
(`TauCeti.isEilenbergMacLaneSpaceOne_cellularClassifyingSpace`).

It is an abbreviation, so the API of `TauCeti.killHomotopyGroups` applies to it directly: it is
Hausdorff and path connected, contains the presentation complex as a closed subspace, and is a
relative CW complex over it. -/
abbrev cellularClassifyingSpace : TopCat.{u} :=
  killHomotopyGroups 2 (TopCat.of (PresentationComplex R)) (PresentationComplex.basepoint R)

end TauCeti
end
end
