@[expose] public section

noncomputable section

namespace ContDiffAt

variable {𝕂 : Type*} [RCLike 𝕂]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]

variable [CompleteSpace E] (f : E → F) {f' : E ≃L[𝕂] F} {a : E} {n : WithTop ℕ∞}

variable {f}

theorem localInverse_apply_image (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E →L[𝕂] F) a) (hn : n ≠ 0) : hf.localInverse hf' hn (f a) = a :=
  (hf.hasStrictFDerivAt' hf' hn).localInverse_apply_image

end ContDiffAt
end
end
