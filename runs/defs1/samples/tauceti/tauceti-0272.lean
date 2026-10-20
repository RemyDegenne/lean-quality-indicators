public section

open CategoryTheory

namespace TauCeti

universe v u

noncomputable section

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

namespace DGHomotopyCategory

/-- Regard an object of a DG homotopy category as an object of the underlying DG category. -/
@[expose] def underlying (X : DGHomotopyCategory R C) : C := X.obj

end DGHomotopyCategory
end
end TauCeti
end
