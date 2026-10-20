@[expose] public section

variable {𝕜 E F G ι : Type*} {M : ι → Type*}

open Function Module Set

open scoped Pointwise Convex

open scoped Convex

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {x y z : 𝕜}

theorem segment_eq_Icc' (x y : 𝕜) : [x -[𝕜] y] = Icc (min x y) (max x y) := by
  rcases le_total x y with h | h
  · rw [segment_eq_Icc h, max_eq_right h, min_eq_left h]
  · rw [segment_symm, segment_eq_Icc h, max_eq_left h, min_eq_right h]

end LinearOrderedField
end
