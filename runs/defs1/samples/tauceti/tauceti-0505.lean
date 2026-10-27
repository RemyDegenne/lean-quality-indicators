public section

namespace TauCeti.SlStd

universe v

open LieAlgebra.SpecialLinear

open scoped Matrix TensorProduct

open scoped CategoryTheory.MonObj

variable (r : ℕ)

/-- The coordinate basis of the standard lattice.

The carrier subtype and `ℤ`-module structure of a submodule are definitionally equal to those of
its underlying additive subgroup, so the restricted-scalars basis has the displayed target type. -/
noncomputable def latticeBasis : Module.Basis (Fin (r + 1)) ℤ (lattice r).toAddSubgroup :=
  TauCeti.coordinateLatticeBasis (Fin (r + 1))

end TauCeti.SlStd
end
