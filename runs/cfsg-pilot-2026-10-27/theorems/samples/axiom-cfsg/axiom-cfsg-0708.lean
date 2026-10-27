open CFSG

namespace CFSG.BenderSuzuki

namespace External

open MatrixGroups

open scoped LinearAlgebra.Projectivization

open scoped Matrix

open scoped commutatorElement

universe u

public theorem hermitianTorusPSU_mul_unipotent
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (k : Kˣ) (z : hermitianUnipotentCoord J) :
    hermitianTorusPSU J hJstandard k * hermitianUnipotentPSU J hJstandard z =
      hermitianUnipotentPSU J hJstandard (hermitianTorusAction J k z) *
        hermitianTorusPSU J hJstandard k := by
  apply Subtype.ext
  change Matrix.ProjGenLinGroup.mk (hermitianTorusGL J k) *
      Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J z) =
    Matrix.ProjGenLinGroup.mk
        (hermitianUnipotentGL J (hermitianTorusAction J k z)) *
      Matrix.ProjGenLinGroup.mk (hermitianTorusGL J k)
  rw [← map_mul, hermitianTorusGL_mul_unipotent, map_mul]

end External
end CFSG.BenderSuzuki
