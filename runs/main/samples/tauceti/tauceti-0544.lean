public section

noncomputable section

namespace LinearPMap

section Basic

variable {𝕜 X : Type*} [Ring 𝕜] [AddCommGroup X] [TopologicalSpace X] [Module 𝕜 X]

variable {A : X →ₗ.[𝕜] X} {lambda : 𝕜} {R : X →L[𝕜] X}

theorem IsResolventAt.smul_sub_injective (h : IsResolventAt A lambda R) :
    Function.Injective fun x : A.domain => lambda • (x : X) - A x := by
  intro x y hxy
  dsimp only at hxy
  exact Subtype.ext (by rw [← h.apply_smul_sub x, ← h.apply_smul_sub y, hxy])

end Basic
end LinearPMap
end
end
