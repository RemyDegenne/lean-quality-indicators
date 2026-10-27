public section

open CategoryTheory

namespace TauCeti

universe v u

noncomputable section

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

/-- A morphism in H⁰(C), using the canonical Mathlib homology object of the DG Hom complex. -/
noncomputable abbrev DGHomotopyClass (X Y : C) :=
  (dgHomComplex R X Y).homology 0

end
end TauCeti
end
