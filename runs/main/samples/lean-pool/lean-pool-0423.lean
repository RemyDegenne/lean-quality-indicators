section

@[expose] public section

noncomputable section

namespace EulerPacketPressure

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketCylinderField EulerPacketTimeProfile EulerPacketShiftArithmetic
  EulerPacketCoarseMajorant EulerPacketFiniteFrequency EulerFiniteGrades

variable {P T : ℝ} [Fact (0 < P)] {N : ℕ} {a : ℕ → Profile} {support : Set Space}
  (hT : 0 < T) (m : Space)
  (G : ∀ i, i ≤ N → ProfileRegularity P T hT.le support (a i))
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ}
  (K : ∀ i, i ≤ N → PressureBudget P T hT.le m (a i) S R i)

variable (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i)
  (hR : 1 ≤ R) (ha : a 0 = 0)

include ha in
theorem covectorGrades_one (hN : 1 ≤ N) (hm : (a 1).meanPressure = 0) :
    covectorGrades N m a 1=angularPressure m (a 1).highPressure := by
  rw [covectorGrades,assemble_interior N 1 le_rfl hN]
  simp only [Nat.sub_self,hm,ha]
  funext z
  simp only [zero_highPressure, Pi.add_apply, pressureGradient, pressureJet_zero, Prod.snd_zero,
      ContinuousLinearMap.zero_comp, map_zero, angularPressure, zero_add, add_zero]

end EulerPacketPressure
end
end
end
