public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace CFSG.Quasithin.Om4Model

open CFSG.Quasithin.SL2Model

section ModuleDecomp2

variable {X : Type*} [AddCommGroup X]

omit [AddCommGroup X] in
theorem conj_invol_ne (τ γ : SL(2, ZMod 2)) (hτ : τ * τ = 1) (hτ' : τ ≠ 1) (hγ : γ ^ 3 = 1)
    (hγ' : γ ≠ 1) : γ * τ * γ⁻¹ ≠ τ := by
  rcases sl2_conj_ne_aux τ γ with h | h | h | h | h
  · exact absurd hτ h
  · exact absurd h hτ'
  · exact absurd hγ h
  · exact absurd h hγ'
  · exact h

end ModuleDecomp2
end CFSG.Quasithin.Om4Model
end
