public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM uN

namespace TauCeti

namespace ReducedTensorWords

section Semiring

variable (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]

theorem eq_of_deconcatenation_eq_of_letter_eq {x y : ReducedTensorWords R M}
    (hd : deconcatenation R M x = deconcatenation R M y) (hl : letter R M x = letter R M y) :
    x = y := by
  apply DirectSum.ext_component R
  intro n
  rw [← DirectSum.apply_eq_component R x n, ← DirectSum.apply_eq_component R y n]
  rw [apply_eq_component R M x n, apply_eq_component R M y n]
  rcases eq_or_ne n 1 with rfl | hn
  · have h := congrArg (TensorPower.oneEquiv R M).symm hl
    rwa [letter_apply, letter_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply] at h
  · have h2 : 2 ≤ n.1 := by
      rcases Nat.lt_or_ge n.1 2 with h | h
      · exact absurd (Subtype.ext (by omega : n.1 = 1)) hn
      · exact h
    refine TensorPower.splitAt_injective R M n.1 1 (by omega) ?_
    have hx := congrArg (fun f ↦ f x) (map_component_deconcatenation R M n h2)
    have hy := congrArg (fun f ↦ f y) (map_component_deconcatenation R M n h2)
    simp only [LinearMap.comp_apply] at hx hy
    rw [← hx, ← hy, hd]

end Semiring
end ReducedTensorWords
end TauCeti
end
