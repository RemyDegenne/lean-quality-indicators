section

@[expose] public section

noncomputable section

namespace NavierStokes.SlotColoring

open Set

open scoped BigOperators

/-- Color, given by `(Fintype.equivFin Palette) (colorData L)`. -/
def color (L : Label) : Fin (Fintype.card Palette) := (Fintype.equivFin Palette) (colorData L)

end NavierStokes.SlotColoring
end
end
end
