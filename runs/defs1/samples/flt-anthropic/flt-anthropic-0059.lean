set_option autoImplicit false

noncomputable section

open KaehlerDifferential TensorProduct

namespace AlgebraicCurve

namespace Differential

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def pullbackAlong (φ : F →ₐ[K] F') : Ω[F⁄K] →ₗ[K] Ω[F'⁄K] :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  (KaehlerDifferential.map K K F F').restrictScalars K

end Differential
end AlgebraicCurve
end
