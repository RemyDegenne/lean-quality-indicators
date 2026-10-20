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

variable [RingHomIsometric σ] [VectorBundle 𝕜 F E] [MemTrivializationAtlas e]

local instance : MemTrivializationAtlas (Trivial.trivialization B 𝕜) := ⟨rfl⟩

theorem continuous_weightedSesquilinearForm
    (q : F →SL[σ] F →L[𝕜] 𝕜) (φ : B → 𝕜) (hφ : Continuous φ)
    (hs : tsupport φ ⊆ e.baseSet) :
    Continuous
      (fun b ↦ TotalSpace.mk' (F →SL[σ] F →L[𝕜] 𝕜) b (e.weightedSesquilinearForm q φ b)) := by
  refine continuous_iff_continuousAt.2 fun b ↦ ?_
  by_cases hb : b ∈ tsupport φ
  · exact continuousAt_weightedSesquilinearForm_of_mem e q φ (hs hb) hφ.continuousAt
  · apply (continuousAt_zeroSection (F := F →SL[σ] F →L[𝕜] 𝕜)
      (E := fun b ↦ E b →SL[σ] E b →L[𝕜] 𝕜) 𝕜 b).congr_of_eventuallyEq
    filter_upwards [eventually_weightedSesquilinearForm_eq_zero e q φ hb] with c hc
    simp only [zeroSection, hc]

end Bundle.Trivialization
end
end
