namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter

open scoped Topology BigOperators ContDiff

open MeasureTheory Filter

open scoped BigOperators

theorem sum_nextCoreObservation_countMoment_le {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (y : Space) (R : ℝ) :
    (∑ c : Fin N → Fin 2, coreLawAverage (nextCoreObservation p hp ψ c)
      (fun φ => rawCountMoment φ y R)) ≤
      coreLawAverage ψ (fun φ => rawCountMoment φ y R) := by
  rw [sum_nextCoreObservation_count_eq hψ p hp y R]
  change (∑ t : Spins M, ∫ v, ∑ c : Fin N → Fin 2,
      coreLawAverage (orderedCutForm p hp (coreSlice ψ t v) c) (fun φ => rawCountMoment φ y R)) ≤
    ∑ t : Spins M, ∫ v, rawCountMoment (coreSlice ψ t v) y R
  apply Finset.sum_le_sum
  intro t _
  apply integral_mono_ae
    (integrable_finsetSum _ (fun c _ => nextCoreObservation_count_statistic_integrable hψ p hp c y R t))
    (rawCountMoment_coreSlice_integrable hψ y R t)
  filter_upwards [hψ.ae_coreSlice t] with v hv
  exact sum_cutCore_countMoment_le hv p hp y R

end CoulombAtom
end
end OAI
