@[expose] public section

open TauCeti.DavisKahan.Angle

open TauCeti.DavisKahan.Sylvester

open scoped InnerProductSpace

namespace TauCeti

namespace DavisKahan

namespace FreeBeam

namespace Model

open DavisKahan1970.Section9

open TauCeti.DavisKahan.TanTheta

open TauCeti.DavisKahan.TanTheta

open TauCeti.DavisKahan.ExactSinTheta

section

open DavisKahan1970.Section9

/-- **The one-dimensional Rayleigh--Ritz trial block at a unit Ritz vector.**  The
compression is the scalar `a = ⟪v, ε t v⟫` and the residual is the single Ritz column. -/
noncomputable def beamColumnBlock (ε : ℝ) (v : BeamL2) (hv : v ∈ beamTrial) (hvnorm : ‖v‖ = 1)
    (a : ℝ) (hform : ⟪v, beamPerturbation ε v⟫_ℂ = ((a : ℝ) : ℂ)) :
    BoundedCompressionTrialBlock (beamPerturbed ε) (ℂ ∙ v) where
  domain_le := fun _ hx => beamTrial_le_domain (span_singleton_le_beamTrial hv hx)
  operator := ((a : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (ℂ ∙ v)
  operator_selfAdjoint := by
    have h1 : IsSelfAdjoint (((a : ℝ) : ℂ)) := by
      change star ((a : ℝ) : ℂ) = ((a : ℝ) : ℂ)
      rw [Complex.star_def, Complex.conj_ofReal]
    have h2 : IsSelfAdjoint (ContinuousLinearMap.id ℂ (ℂ ∙ v)) := by
      rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
      intro x y
      rfl
    exact h1.smul h2
  operator_apply := fun x => by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 x.2
    have hxv : (x : BeamL2) = c • v := hc.symm
    have hmem : (x : BeamL2) ∈ beamTrial := span_singleton_le_beamTrial hv x.2
    change ((a : ℝ) : ℂ) • (x : BeamL2) = _
    rw [beamPerturbed_apply_of_mem_beamTrial ε hmem,
      Submodule.starProjection_unit_singleton ℂ hvnorm, hxv, map_smul,
      inner_smul_right, hform]
    module
  residual := beamPerturbation ε ∘L (ℂ ∙ v).subtypeL - ((a : ℝ) : ℂ) • (ℂ ∙ v).subtypeL
  residual_apply := fun x => by
    have hmem : (x : BeamL2) ∈ beamTrial := span_singleton_le_beamTrial hv x.2
    change beamPerturbation ε (x : BeamL2) - ((a : ℝ) : ℂ) • (x : BeamL2) = _
    rw [beamPerturbed_apply_of_mem_beamTrial ε hmem]
    rfl

end
end Model
end FreeBeam
end DavisKahan
end TauCeti
end
