@[expose] public section

open Function Monoid.Coprod Quiver

noncomputable section

namespace MarshallHall

namespace GeneralGrushko

universe u v w

variable {G H : Type u} {V : Type v} [Group G] [Group H] [Quiver V]
  [HasInvolutiveReverse V]

namespace BinaryLabelling

variable (L : BinaryLabelling (G := G) (H := H) (V := V))

/-- A nonempty monochromatic piece of a symmetrized path, with its endpoints and factor recorded. -/
structure SymmRunPiece where
  /-- The starting vertex of the monochromatic path piece. -/
  source : Symmetrify V
  /-- The ending vertex of the monochromatic path piece. -/
  target : Symmetrify V
  /-- The nonempty path underlying the monochromatic piece. -/
  path : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) source target
  /-- The factor containing every label of the path piece. -/
  color : Bool
  monochromatic : L.symmIsMonochromatic path color
  nonempty : path.length ≠ 0

end BinaryLabelling
end GeneralGrushko
end MarshallHall
end
end
