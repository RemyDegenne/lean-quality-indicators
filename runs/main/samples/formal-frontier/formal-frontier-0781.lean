@[expose] public section

noncomputable section

open Bundle Set Topology

open scoped Bundle

namespace Bundle.Trivialization

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type*}
  [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E]
  (e : Trivialization F (π F E)) {σ : 𝕜 →+* 𝕜}

section

variable [e.IsLinear 𝕜]

@[simp]
theorem weightedBilinearForm_apply (q : F →L[𝕜] F →L[𝕜] 𝕜) (φ : B → 𝕜)
    (b : B) (v w : E b) :
    e.weightedBilinearForm q φ b v w =
      φ b * q (e.continuousLinearMapAt 𝕜 b v) (e.continuousLinearMapAt 𝕜 b w) :=
  e.weightedSesquilinearForm_apply q φ b v w

end
end Bundle.Trivialization
end
end
