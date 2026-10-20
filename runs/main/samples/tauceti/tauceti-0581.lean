public section

namespace WeierstrassCurve

variable {R : Type*} [CommSemiring R]

variable (W : WeierstrassCurve R)

@[simp]
theorem formalWCoeff_three : formalWCoeff W 3 = 1 := by
  rw [formalWCoeff_eq_step]; rfl

end WeierstrassCurve
end
