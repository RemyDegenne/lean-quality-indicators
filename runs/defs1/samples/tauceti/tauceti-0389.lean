public section

namespace WeierstrassCurve.Affine

namespace Point

variable {F : Type*} [Field F] [DecidableEq F]
  (W : WeierstrassCurve F) (C : VariableChange F)

/-- The group isomorphism `(C • W).Point ≃+ W.Point` induced by the admissible change of
variables; its underlying bijection is `equivVariableChange`. -/
def addEquivVariableChange : (C • W).toAffine.Point ≃+ W.toAffine.Point where
  __ := equivVariableChange W C
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    simp only [Equiv.toFun_as_coe, equivVariableChange_some]
    by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
    · rw [add_of_Y_eq hxy.1 hxy.2]
      refine (add_of_Y_eq ?_ ?_).symm
      · rw [hxy.1]
      · rw [variableChange_negY, hxy.2, hxy.1]
    · rw [add_some hxy, equivVariableChange_some, add_some (variableChange_negY_ne W C hxy)]
      simp only [variableChange_slope W C h₁.1 h₂.1 hxy, variableChange_addX, variableChange_addY]

end Point
end WeierstrassCurve.Affine
end
