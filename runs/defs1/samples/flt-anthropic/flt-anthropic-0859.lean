set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

section AlongPlaces

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def Place.ramificationIndexAlong (φ : F →ₐ[K] F') (w : Place K F') : ℕ :=
  letI := algebraAlong φ
  w.ramificationIndex F

end AlongPlaces
end AlgebraicCurve
end
