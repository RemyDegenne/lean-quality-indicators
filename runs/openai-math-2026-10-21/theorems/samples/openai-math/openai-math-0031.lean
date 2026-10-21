namespace OAI

section

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal Topology

open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem cap_family_gainLoss_uniformIntegrable {s₀ η K α γ d₀ q T : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (F : ∀ N, Approximation s₀ η K α γ d₀ q T N) :
    UniformIntegrable (fun (N : ℕ) => CollisionCompactness.gainDensity (torusPhysical q (F N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UniformIntegrable (fun (N : ℕ) => CollisionCompactness.lossDensity (torusPhysical q (F N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) := by
  have hδ (n) : 0 < DatumBounds.scale s₀ η (n+1) := DatumBounds.scale_pos hs₀ _
  have hδmax (n) : DatumBounds.scale s₀ η (n+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (n+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hhn (n) (p) : 0 ≤ (F n).coefficient*
      HotSeedProfile.normalized q (DatumBounds.scale s₀ η (n+1)) p := by
    obtain ⟨_,_,hb⟩ := HotSeedProfile.normalized_bounds (hδ n) (hδmax n) q
    exact mul_nonneg (F n).coefficient_mem.1 (hb p).1
  exact capped_family_gainLoss_uniformIntegrable hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq hT hTmax (fun n => n+1) (fun n => damping q (n+1) (F n).amplitude)
    (fun n => 2*(F n).amplitude) (fun n => DatumBounds.scale s₀ η (n+1))
    (fun n p => (F n).coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (n+1)) p)
    (fun _ => by positivity) (fun n => (bounds (by positivity) (F n).amplitude_pos).1)
    (fun n => mul_nonneg (by norm_num) (F n).amplitude_pos.le) hδ hδmax (fun _ => le_rfl)
    (fun n => (HotSeedProfile.normalized_measurable q _).const_mul _) hhn
    (fun n => (F n).initial_bound) (fun n => (F n).solution) (fun n => (F n).cap_bound)

end BoltzmannNonuniqueness.JetCopyDatum.BelowCap
end
end
end OAI
