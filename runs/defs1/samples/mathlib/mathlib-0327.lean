@[expose] public section

section RealImaginaryPart

open Complex

variable {A : Type*}

section AddCommGroup

variable [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]

/-- The real part `ℜ a` of an element `a` of a star module over `ℂ`, as a linear map. This is just
`selfAdjointPart ℝ`, but we provide it as a separate definition in order to link it with lemmas
concerning the `imaginaryPart`, which doesn't exist in star modules over other rings. -/
noncomputable def realPart : A →ₗ[ℝ] selfAdjoint A :=
  selfAdjointPart ℝ

end AddCommGroup
end RealImaginaryPart
end
