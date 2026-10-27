@[expose] public section

noncomputable section

namespace EulerParentPacketFrames

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerTransversePacketProvider EulerTransverseFrameCoordinates EulerVolterraConvolution
  EulerPacketSourceGeometry EulerPacketNormalizedPrimary EulerPacketMovingFrame
  EulerPacketPrimaryShear EulerPacketRay

open scoped ContDiff

namespace Parent

variable (G : Parent)

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (D : Data V) (hTime : D.T = G.T) (τ : ℝ) (hτ : 0 ≤ τ)

/-- The only error input is the literal center derivative estimate for
the already constructed perturbation. No ray, velocity or matrix ODE
is supplied as a hypothesis. -/
def geometryFrameOfCenterExpansion (η : U) (hη : η ≠ 0)
    (w : ℝ → Space → Space) (c CM CH K error : ℝ)
    (hCM : 0 ≤ CM) (hK : 1 ≤ K) (he : 0 ≤ error)
    (hMK : CM ≤ K) (hHK : CM ^ 2 + CH ≤ K ^ 2)
    (hM : ∀ t ∈ Icc τ D.T, ‖G.centerStrain t‖ ≤ CM)
    (hH : ∀ t ∈ Icc τ D.T, ‖G.centerCurvature t‖ ≤ CH)
    (hupdate : ∀ t : Icc (0 : ℝ) D.T,
      D.M.field t 0 = G.centerStrain t+fderiv ℝ (w t) 0)
    (hpacket : ∀ t ∈ Icc τ D.T,
      ‖fderiv ℝ (w t) 0-c • rankOne (E := Space) (F := Space) ℝ
          (G.sourceVelocity m hm R S hS η t) (G.sourceNormal m t)‖ ≤
          error) :
    ParentFrame D τ where
  B := G.centerStrain
  B₁ := G.centerStrainDerivative
  m := G.sourceNormal m
  v := G.sourceVelocity m hm R S hS η
  c := c
  G := K
  error := error
  G_lower := hK
  error_nonneg := he
  B_derivative t ht := by
    rw [hTime] at ht ⊢
    exact G.centerStrain_derivative τ hτ t ht
  ray_equation t ht := by
    have ht0 : t ∈ Icc (0 : ℝ) G.T := ⟨hτ.trans ht.1,by simpa only [hTime] using ht.2⟩
    exact (G.sourceNormal_equation m ⟨t,ht0⟩).mono
      (fun r hr => ⟨hτ.trans hr.1,by simpa only [hTime] using hr.2⟩)
  velocity_equation t ht := by
    have ht0 : t ∈ Icc (0 : ℝ) G.T := ⟨hτ.trans ht.1,by simpa only [hTime] using ht.2⟩
    have h := G.sourceVelocity_equation m hm R S hS η ⟨t,ht0⟩
    dsimp only at h
    exact h.mono (fun r hr => ⟨hτ.trans hr.1,by simpa only [hTime] using hr.2⟩)
  ray_nonzero t ht := by
    have hm0 : m ≠ 0 := by intro h; simp [h] at hm
    exact G.sourceNormal_ne_zero m hm0 ⟨t,hτ.trans ht.1,by simpa only [hTime] using ht.2⟩
  velocity_nonzero t ht :=
    G.sourceVelocity_ne_zero m hm R S hS η hη ⟨t,hτ.trans ht.1,by simpa only [hTime] using ht.2⟩
  tangent t ht :=
    G.sourceVelocity_tangent m hm R S hS η ⟨t,hτ.trans ht.1,by simpa only [hTime] using ht.2⟩
  B_bound t ht := (hM t ht).trans hMK
  B₁_bound t ht := by
    rw [hTime] at hM hH ht
    exact G.centerStrainDerivative_bound τ CM CH K hτ hCM hM hH hHK t ht
  remainder_bound t ht := by
    have htD : t ∈ Icc (0 : ℝ) D.T := ⟨hτ.trans ht.1,ht.2⟩
    have htG : t ∈ Icc (0 : ℝ) G.T := by simpa only [hTime] using htD
    have hm0 : m ≠ 0 := by intro h; simp [h] at hm
    have hn := G.sourceNormal_ne_zero m hm0 ⟨t,htG⟩
    have hv := G.sourceVelocity_ne_zero m hm R S hS η hη ⟨t,htG⟩
    have hc := rankOne_normalized c (G.sourceVelocity m hm R S hS η t) (G.sourceNormal m t) hv hn
    have hu := hupdate ⟨t,htD⟩
    rw [show D.clamp t = ⟨t,htD⟩ from Data.clamp_coe D ⟨t,htD⟩,hu,
      add_sub_cancel_left,primaryShear,← hc]
    exact hpacket t ht

end Parent
end EulerParentPacketFrames
end
end
