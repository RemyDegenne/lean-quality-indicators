@[expose] public section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology

open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Endgame

theorem regular_point_of_holder_norm
    {Ω : Set Vec3} {I : Set ℝ} {U V : Set ParabolicPoint}
    {u w : ParabolicPoint → Vec3} {z : ParabolicPoint} {γ C : ℝ}
    (hV : IsOpen V) (hz : z ∈ V) (hVU : V ⊆ U)
    (hVΩ : V ⊆ spaceTimeSet Ω I) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hwu : w =ᵐ[volume.restrict U] u) (hw : ParabolicHolderVecNormLE U w γ C) :
    IsRegularPoint Ω I u z := by
  exact regular_point_of_holder_on_open hV hz hVΩ hγ hγ1
    (ae_restrict_of_ae_restrict_of_subset hVU hwu)
    (holder_on_of_norm (holder_norm_mono hw hVU))

end CKN.Core.Endgame
end
end
