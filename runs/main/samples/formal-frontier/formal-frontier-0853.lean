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

theorem weightedSesquilinearForm_eq_zero_of_notMem_baseSet
    (q : F →SL[σ] F →L[𝕜] 𝕜) (φ : B → 𝕜) {b : B} (hb : b ∉ e.baseSet) :
    e.weightedSesquilinearForm q φ b = 0 := by
  ext v w
  simp [continuousLinearMapAt_apply, linearMapAt_def_of_notMem e hb]

end
end Bundle.Trivialization
end
end
