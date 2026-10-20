public section

open Module Matrix

namespace TauCeti.IntegralLattice

universe u v w

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

variable {W : Type w} [AddCommGroup W] [Module ℚ W]

section GramMatrix

variable (L : IntegralLattice V)

theorem gramDet_def {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) :
    L.gramDet e = Matrix.det (L.gramMatrix e) :=
  (rfl)

end GramMatrix
end TauCeti.IntegralLattice
end
