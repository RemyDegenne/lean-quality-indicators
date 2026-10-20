@[expose] public section

namespace NRR.Geometry

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

@[simp] theorem neg_carrier (K : ConvexBody E) :
    (K.neg : Set E) = Neg.neg '' (K : Set E) := rfl

end ConvexBody
end NRR.Geometry
end
