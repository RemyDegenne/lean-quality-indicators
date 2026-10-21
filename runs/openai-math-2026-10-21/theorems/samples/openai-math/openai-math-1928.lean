namespace OAI

noncomputable section

open MeasureTheory Set

open scoped ContDiff

namespace CubicFirstMoment

lemma cubicThetaDualMellinKernel_eq {q : Eisenstein} (hq : primary q)
    (ℓ : ℤ) (W : ℝ→ℂ) {Z : ℝ} (hZ : 0<Z) (s : ℂ) :
    cubicThetaDualMellinKernel q ℓ W Z s =
      mellin W s*(Z:ℂ)^s*(cubicThetaLevelScale q:ℂ)^(4*s-2)*
        ((2*Real.pi:ℝ):ℂ)^(4*s-2)*metaplecticGammaQuotient ℓ s := by
  calc
    _ = mellin W s*(cubicThetaDualPrefactor q*(cubicThetaDualScale q Z:ℂ)^s)*
        metaplecticGammaQuotient ℓ s := by unfold cubicThetaDualMellinKernel; ring
    _ = _ := by rw [←cubicTheta_archimedean_power hq hZ]; ring

end CubicFirstMoment
end
end OAI
