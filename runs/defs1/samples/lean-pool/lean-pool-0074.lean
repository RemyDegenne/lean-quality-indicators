@[expose] public section

open Set Convexity

namespace SphereOddDegree

/-- The one-dimensional finite coordinate simplex is the unit interval. -/
noncomputable def FiniteSimplex.homeomorphUnitInterval :
    finiteSimplex ℝ (Fin 2) ≃ₜ unitInterval where
  toFun s := ⟨s.val 1, s.2.1 1, FiniteSimplex.le_one s 1⟩
  invFun t := ⟨![1 - t, t], Fin.forall_fin_two.2
    ⟨sub_nonneg.mpr t.2.2, t.2.1⟩, by simp⟩
  left_inv s := by
    apply Subtype.ext
    funext i
    have hsum : s.val 0 + s.val 1 = 1 := by simpa using s.2.2
    fin_cases i
    · simp
      linarith
    · simp
  right_inv t := by apply Subtype.ext; rfl
  continuous_toFun := ((continuous_apply 1).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by fun_prop

end SphereOddDegree
end
