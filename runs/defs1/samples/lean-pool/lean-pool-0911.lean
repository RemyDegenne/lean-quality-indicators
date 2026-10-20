@[expose] public section

noncomputable section

namespace EulerParentPacketFrames

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerLpTranslation
  EulerPacketParentLabelBounds EulerTimeIntervalRestriction EulerTransversePacketProvider
  EulerPacketSourcePropagator EulerVolterraConvolution EulerTransverseSourceCoefficientPath

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

namespace LabelData

variable {G : Parent} (L : LabelData G) (H : LowBounds G)
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)
  (Ti Cp : ℝ) (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti) (hCp : 0 ≤ Cp)
  (g : C(Icc (0 : ℝ) (G.T - τ), ℝ)) (hg : ∀ t, 0 < g t)
  (hg0 : g ⟨0, le_rfl, (sub_pos.mpr hτT).le⟩ = 1)
  (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
  (hsub : S ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))
  (hphysical : PhysicalGrowth ((G.transverseData m hm R S hS).tail τ hτ.le hτT)
    EulerPacketParentPhysicalBudgets.halfBall g Cp)

/-- Joined inputs as an element of `JoinedInputs (G.meanData H) (G.transverseData m hm R S hS) τ
hτ hτT (G.historyOn H m hm R S hS τ hτ hτT)`. -/
def joinedInputs (TiTotal : ℝ) (hT1 : G.T ≤ 1) (hTiTotal : G.T⁻¹ ≤ TiTotal) :
    JoinedInputs (G.meanData H) (G.transverseData m hm R S hS) τ hτ hτT
      (G.historyOn H m hm R S hS τ hτ hτT) := by
  let A := L.joinedRaw H m hm R S hS τ hτ hτT Ti Cp hτ1 hTi hCp g hg hg0 Ω hΩ hΩo hsub hΩball
      hphysical
  let N := L.normalBudget m hm R S hS 6
  let M := L.meanBudget H 6 TiTotal hT1 hTiTotal
  let Rn := EulerPacketParentNormalBudget.radius (coefficientRadius L.K)
    (frameAmplitude L.K) (gradientAmplitude L.K)
  let Rm := EulerPacketParentMeanBudget.radius 6 G.T TiTotal (coefficientRadius L.K)
    (frameAmplitude L.K) (gradientAmplitude L.K) (gradientAmplitude L.K) H.L
  let Rc := max A.R (max Rn Rm)
  exact {
    linear := A.enlargeRadius Rc (le_max_left _ _)
    normal := N.enlargeRadius Rc ((le_max_left Rn Rm).trans (le_max_right _ _))
    mean := M.enlargeRadius Rc ((le_max_right Rn Rm).trans (le_max_right _ _)) }

end LabelData
end EulerParentPacketFrames
end
end
