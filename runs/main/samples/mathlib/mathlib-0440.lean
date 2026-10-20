@[expose] public section

noncomputable section

open Module Complex

open scoped Real RealInnerProductSpace ComplexConjugate

namespace Orientation

attribute [local instance] Complex.finrank_real_complex_fact

variable {V V' : Type*}

variable [NormedAddCommGroup V] [NormedAddCommGroup V']

variable [InnerProductSpace ℝ V] [InnerProductSpace ℝ V']

variable [Fact (finrank ℝ V = 2)] [Fact (finrank ℝ V' = 2)] (o : Orientation ℝ V (Fin 2))

local notation "J" => o.rightAngleRotation

@[simp]
theorem rotation_pi : o.rotation π = LinearIsometryEquiv.neg ℝ := by
  ext x
  simp [rotation]

end Orientation
end
end
