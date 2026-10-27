public section

namespace TauCeti.SlStd

universe v

open LieAlgebra.SpecialLinear

open scoped Matrix TensorProduct

open scoped CategoryTheory.MonObj

variable (r : ℕ)

section Carrier

open AlgebraicGeometry CategoryTheory

attribute [local instance high] Algebra.toModule

/-- The `A`-valued points of the type `A_r` carrier, as matrices. -/
noncomputable def points (A : Type v) [CommRing A] :
    Subgroup (Matrix.GeneralLinearGroup (Fin (r + 1)) A) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup (rootGenerator r)
    (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A

end Carrier
end TauCeti.SlStd
end
