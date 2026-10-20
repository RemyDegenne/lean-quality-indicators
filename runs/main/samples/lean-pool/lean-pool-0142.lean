@[expose] public section

namespace UnrestrictedBooleanMul

namespace N4

noncomputable section

@[simp] theorem anfThreeProjection_sliceInfinityQuadraticANF :
    anfThreeProjection sliceInfinityQuadraticANF = 0 :=
  anfThreeProjection_linear_mul_linear (placeA 2) (placeB 2)

end
end N4
end UnrestrictedBooleanMul
end
