public section

open Metric Set Topology

open scoped NNReal

noncomputable section

namespace ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

variable {K α ε : ℝ≥0} (A P : X →L[ℝ] X) (N : X → X) (r : ℝ)

variable (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X,
      ‖NormedSpace.exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X,
      ‖NormedSpace.exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hr : 0 ≤ r) (hN : LipschitzOnWith ε N (closedBall 0 r))
    (hsmall : 2 * K * (ε * 2) < α) (hN0 : N 0 = 0)
    (hP : IsIdempotentElem P) (hAP : Commute A P) {ρ : ℝ}
    (hρ : (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ρ ≤ r)

/-- The local stable set of confined forward solutions, truncated by the norm of its stable
projection, is homeomorphic to the corresponding closed ball in the stable spectral subspace. -/
noncomputable def localStableSetHomeomorph :
    {v : range P | ‖(v : X)‖ ≤ ρ} ≃ₜ
      {x : X | (∃ y : ℝ → X, IsIntegralCurveOn y (fun _ z ↦ A z + N z) (Ici 0) ∧
          y 0 = x ∧ MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖P x‖ ≤ ρ} :=
  -- `graphHomeomorph` takes a preimage of the closed ball; this equality identifies
  -- that preimage with the norm bound in the domain of this homeomorphism.
  (Homeomorph.setCongr (show {v : range P | ‖(v : X)‖ ≤ ρ} =
      Subtype.val ⁻¹' closedBall 0 ρ by
    ext v
    simp only [mem_ofPred_eq, mem_preimage, mem_closedBall_zero_iff])).trans <|
    (graphHomeomorph P hP (localStableGraphMap A P N r hs hu hr hN hsmall)
      (fun v _ ↦ apply_localStableGraphMap hs hu hr hN hsmall hP hAP v)
      (lipschitzWith_localStableGraphMap hs hu hr hN hsmall).continuous.continuousOn _).trans <|
    Homeomorph.setCongr
      (setOf_exists_isIntegralCurveOn_mapsTo_closedBall_eq_image hs hu hr hN hsmall
        hN0 hP hAP hρ).symm

end ContinuousLinearMap
end
end
