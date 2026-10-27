public section

namespace TauCeti

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

variable {W : Type v} [AddCommGroup W] [Module ℚ W]

namespace IntegralLattice

/-- The norm ideal of the integral form of a lattice. -/
noncomputable abbrev normIdeal (L : IntegralLattice V) : Ideal ℤ :=
  L.integralForm.normIdeal

end IntegralLattice
end TauCeti
end
