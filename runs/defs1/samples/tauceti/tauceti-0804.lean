public noncomputable section

open Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GL2

open scoped MatrixGroups

namespace TauCeti

variable (N : ℕ) [NeZero N] (k : ℤ)

namespace Newform

variable {N k}

/-- A newform's eigenvalue character on the integral newspace Hecke algebra, obtained by
restricting its complex character. -/
def heckeTDiamondCuspNewIntegralCharacter (f : Newform N k) :
    heckeTDiamondCuspNewIntegralAlgebra N k →ₐ[ℤ] ℂ :=
  ((heckeTDiamondCuspNewCharacter f).restrictScalars ℤ).comp
    (heckeTDiamondCuspNewIntegralAlgebraToComplex N k)

end Newform
end TauCeti
end
