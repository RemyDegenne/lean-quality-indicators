public section

open CategoryTheory Matrix WithConv

namespace TauCeti.ProjectiveGeneralLinear

universe u v

noncomputable section

/-- The weights of the diagonal projective torus on the matrix units, with the
last diagonal coordinate normalized to one. -/
def diagonalTorusWeight (r : ℕ) (a : Fin ((r + 1) * (r + 1))) :
    ULift.{u} (Fin r) → ℤ :=
  diagonalLiftWeight r (finProdFinEquiv.symm a).1 -
    diagonalLiftWeight r (finProdFinEquiv.symm a).2

end
end TauCeti.ProjectiveGeneralLinear
end
