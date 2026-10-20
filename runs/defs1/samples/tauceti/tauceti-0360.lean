public section

open Module Matrix

namespace TauCeti.IntegralLattice

universe u v w

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

variable {W : Type w} [AddCommGroup W] [Module ℚ W]

section Invariants

/-- The basis-independent signed determinant of an integral lattice. -/
noncomputable def determinant (L : IntegralLattice V) : ℤ :=
  L.gramDet (Module.Free.chooseBasis ℤ L)

end Invariants
end TauCeti.IntegralLattice
end
