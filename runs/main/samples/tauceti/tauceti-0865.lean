public section

namespace Complex

variable (X : Type*) [AddCommGroup X] [TopologicalSpace X] [Module ℂ X]
  [ContinuousConstSMul ℂ X]

variable {X}

@[simp]
theorem smulIEquiv_apply (x : X) : smulIEquiv X x = I • x := by
  simp [smulIEquiv, Units.smul_def]

end Complex
end
