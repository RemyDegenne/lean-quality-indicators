@[expose] public section

universe u v w w₁

namespace CoalgEquiv

variable {K : Type u} {C : Type v} {C' : Type w}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

variable [AddCommGroup C'] [Module K C'] [Coalgebra K C']

@[simp]
theorem subcoalgebraCongr_apply (e : C ≃ₗc[K] C') (D : Subcoalgebra K C) :
    e.subcoalgebraCongr D = Subcoalgebra.map e.toCoalgHom D := by
  rfl

end CoalgEquiv
end
