namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory

open scoped Topology ContDiff

namespace RVM

lemma spatiallySmooth_time_derivatives_smooth {s : Solution} {T : ℝ} (hT : 0<T)
    (hf : SpatiallySmoothSlab T s.f) (hE : SpatiallySmoothSlab T s.E) (hB : SpatiallySmoothSlab T s.B)
    (hc : ∃ K : Set Phase, IsCompact K ∧ ∀ t∈Icc 0 T, tsupport (fun z => s.f (t,z)) ⊆ K)
    (hft : ∀ t∈Icc 0 T, ∀ z, HasDerivWithinAt (fun r => s.f (r,z)) (slabParticleRHS s (t,z)) (Icc 0 T) t)
    (hEt : ∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt (fun r => s.E (r,x)) (slabElectricRHS s (t,x)) (Icc 0 T) t)
    (hBt : ∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt (fun r => s.B (r,x)) (slabMagneticRHS s (t,x)) (Icc 0 T) t) :
    ContDiffOn ℝ ∞ s.f (particleSlab T) ∧ ContDiffOn ℝ ∞ s.E (fieldSlab T) ∧
      ContDiffOn ℝ ∞ s.B (fieldSlab T) := by
  have hh (n : ℕ) : SpatialJetRegular n (Icc 0 T) s.f ∧
      SpatialJetRegular n (Icc 0 T) s.E ∧ SpatialJetRegular n (Icc 0 T) s.B := by
    induction n with
    | zero => exact ⟨hf.spatialJetRegular,hE.spatialJetRegular,hB.spatialJetRegular⟩
    | succ n ih =>
      exact ⟨spatialJetRegular_succ hT n ih.1 (slabParticleRHS_regular ih.1 ih.2.1 ih.2.2) hft,
        spatialJetRegular_succ hT n ih.2.1 (slabElectricRHS_regular hT n ih.1 ih.2.2 hc) hEt,
        spatialJetRegular_succ hT n ih.2.2 (slabMagneticRHS_regular ih.2.1) hBt⟩
  refine ⟨?_,?_,?_⟩ <;> rw [contDiffOn_infty]
  · exact fun n => (hh n).1.regular
  · exact fun n => (hh n).2.1.regular
  · exact fun n => (hh n).2.2.regular

end RVM
end
end OAI
