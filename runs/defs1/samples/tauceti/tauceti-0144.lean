public section

open Module Matrix

namespace TauCeti.IntegralLattice

universe u v w

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

variable {W : Type w} [AddCommGroup W] [Module ℚ W]

section Invariants

/-- The signed Gram determinant of a nondegenerate integral lattice, regarded as a nonzero
rational number. -/
noncomputable def determinantUnit (L : IntegralLattice V) [L.IsNondegenerate] : ℚˣ :=
  Units.mk0 (L.determinant : ℚ) <| by
    exact_mod_cast (L.determinant_ne_zero_iff.mpr L.form_nondegenerate)

end Invariants
end TauCeti.IntegralLattice
end
