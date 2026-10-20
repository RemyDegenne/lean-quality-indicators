@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization

open AVenhance.Infra.Torus

namespace AVenhance.Infra.Heat

theorem WeakFourier.heatWeak_torusCharacter_line_eq {n : ℕ} (i : Fin (n + 1))
    (k : Fin (n + 1) → ℤ) (z : Vec n) (t : ℝ) :
    torusCharacter k (i.insertNth t z) =
      fourier (-(k i)) (t : UnitAddCircle) *
        ∏ j : Fin n, fourier (-(k (i.succAbove j))) (z j : UnitAddCircle) := by
  simp [torusCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    toUnitTorus, i.prod_univ_succAbove]

end AVenhance.Infra.Heat
end
end
