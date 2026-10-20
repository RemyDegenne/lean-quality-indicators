@[expose] public section

noncomputable section

open MeasureTheory Set Filter

open Homogenization

open AVenhance.Infra.Torus

open scoped Topology

namespace AVenhance.Infra.Section4

theorem theta_energy_hasDerivAt {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x in AVenhance.unitCube, (u s x) ^ 2)
      (∫ x in AVenhance.unitCube, 2 * u t x * classicalTimePartial u (t, x)) t := by
  simpa only [classicalTimePartial, Measure.restrict_congr_set unitCell_ae_eq_unitCube] using
    (AVenhance.Infra.Classical.unitCell_energy_hasDerivAt hu ht)

end AVenhance.Infra.Section4
end
end
