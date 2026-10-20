@[expose] public section

namespace UnrestrictedBooleanMul

namespace N4

noncomputable section

@[simp] theorem f2_mul_self_quartic (u : F₂) : u * u = u := by
  rcases f2_eq_zero_or_one u with rfl | rfl <;> simp

end
end N4
end UnrestrictedBooleanMul
end
