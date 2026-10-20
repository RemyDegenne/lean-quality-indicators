public section

open Module Matrix

namespace TauCeti.IntegralLattice

universe u v w

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

variable {W : Type w} [AddCommGroup W] [Module ℚ W]

namespace Isometry

variable {L : IntegralLattice V} {M : IntegralLattice W}

theorem discriminant_eq (e : Isometry L M) : L.discriminant = M.discriminant := by
  rw [L.discriminant_def, M.discriminant_def, e.determinant_eq]

end Isometry
end TauCeti.IntegralLattice
end
