@[expose] public section

section RealImaginaryPart

open Complex

variable {A : Type*}

section AddCommGroup

variable [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]

@[inherit_doc]
scoped[ComplexStarModule] notation "ℜ" => realPart

@[inherit_doc]
scoped[ComplexStarModule] notation "ℑ" => imaginaryPart

open ComplexStarModule

theorem imaginaryPart_apply_coe (a : A) : (ℑ a : A) = -I • (2 : ℝ)⁻¹ • (a - star a) := by
  simp [imaginaryPart]

end AddCommGroup
end RealImaginaryPart
end
