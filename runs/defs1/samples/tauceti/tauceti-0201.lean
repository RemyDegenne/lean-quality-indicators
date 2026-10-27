public section

namespace TauCeti

open QuadraticMap

universe u v

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

variable {W : Type v} [AddCommGroup W] [Module ℚ W]

/-- An integral lattice is negative-definite when the negative of its quadratic form is
positive-definite. -/
abbrev IsNegDef : Prop := (-L.form.toQuadraticMap).PosDef

end IntegralLattice
end TauCeti
end
