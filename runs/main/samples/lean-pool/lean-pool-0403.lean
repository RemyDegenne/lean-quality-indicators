@[expose] public section

open TauCeti.DavisKahan.Sylvester

open scoped InnerProductSpace Topology

open Filter

namespace TauCeti

namespace DavisKahan

namespace ExactSinTheta

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem spectraBoundedTruncation_upperBound
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) {c : ℝ} (hc : TauCeti.LinearPMap.SemiboundedAbove A c) {τ : ℝ} (x : H) :
    RCLike.re ⟪spectraBoundedTruncation A hA τ x, spectraSpectralCutoff A hA τ x⟫_ℂ ≤
      c * ‖spectraSpectralCutoff A hA τ x‖ ^ 2 := by
  obtain ⟨hx, hb⟩ := TauCeti.LinearPMap.truncation_eq_on_specProjection hA
    (Set.Icc (-τ) τ) measurableSet_Icc (abs_le_max_zero_of_mem_Icc τ) x
  rw [show spectraBoundedTruncation A hA τ x = A ⟨_, hx⟩ from hb.symm]
  exact hc ⟨spectraSpectralCutoff A hA τ x, hx⟩

end ExactSinTheta
end DavisKahan
end TauCeti
end
