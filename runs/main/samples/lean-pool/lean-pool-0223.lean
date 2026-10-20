@[expose] public section

open TauCeti.DavisKahan.Sylvester

open scoped InnerProductSpace

namespace TauCeti

namespace DavisKahan

namespace ExactSinTheta

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

open TauCeti.DavisKahan

noncomputable local instance completeSpaceOfHasOrthogonalProjection
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

section Real

variable {ER FR : Type v}
  [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [CompleteSpace ER]
  [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [CompleteSpace FR]

theorem generalizedSinTheta_unbounded_real_reducingSubspace
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (A : ER →ₗ.[ℝ] ER)
    (hAdense : Dense (A.domain : Set ER)) (hAclosed : A.IsClosed)
    (hA : _root_.IsSelfAdjoint A)
    (U : Submodule ℝ ER) [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (A0 : FR →ₗ.[ℝ] FR)
    (hA0dense : Dense (A0.domain : Set FR)) (hA0closed : A0.IsClosed)
    (hA0 : _root_.IsSelfAdjoint A0)
    (X Rop : FR →L[ℝ] ER)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hXdom : ∀ x : A0.domain, X (x : FR) ∈ A.domain)
    (hReq : ∀ x : A0.domain,
      A ⟨X (x : FR), hXdom x⟩ - X (A0 x) = Rop (x : FR))
    (hgap : FormBoundedSylvesterGap A0
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) δ)
    (hR : N.Mem Rop) :
    N.Mem
        (directedSinThetaOperatorReal X U.subtypeL hframe hε) ∧
      δ * ε * N.gauge
          (directedSinThetaOperatorReal X U.subtypeL hframe hε)
        ≤ N.gauge Rop := by
  let P : NaturalReducingGeneralSinThetaProblem
      (𝕜 := ℝ) (E := ER) (F := FR) N U :=
    { A := A
      A_dense := hAdense
      A_closed := hAclosed
      ambient_selfAdjoint := hA
      reduces := hred
      A₀ := A0
      A₀_dense := hA0dense
      A₀_closed := hA0closed
      trial_selfAdjoint := hA0
      X := X
      residual := Rop
      X_maps_domain := hXdom
      residual_eq := hReq
      gap := δ
      frameLowerBound := ε
      gap_pos := hδ
      frameLowerBound_pos := hε
      lowerFrame := hframe
      spectral_gap := hgap
      residual_mem := hR }
  exact P.result_real N

end Real
end
end ExactSinTheta
end DavisKahan
end TauCeti
end
