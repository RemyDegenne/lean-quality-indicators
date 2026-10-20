public section

namespace TauCeti

open QuadraticMap

universe u v

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

variable {W : Type v} [AddCommGroup W] [Module ℚ W]

@[simp]
theorem radical_toQuadraticMap : L.form.toQuadraticMap.radical = L.radical :=
  LinearMap.BilinForm.radical_toQuadraticMap L.form L.isSymm

end IntegralLattice
end TauCeti
end
