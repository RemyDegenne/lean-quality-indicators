namespace P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X

universe u

noncomputable section

p2m_reactivate

namespace ModularCurve

p2m_open

noncomputable section

namespace UVCrossingModel

p2m_open

open SymmetricTwoVars

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Surjectivity

variable {W : Type u} [CommRing W]

theorem fixedSubring_le_range_chartHom {π : W} [IsPrecomplete (Ideal.span {π}) W]
    (hreg : ∀ h : MvPowerSeries (Fin 2) W,
      h * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
        - MvPowerSeries.C π) = 0 → h = 0)
    (htwo : ∀ w : W, w + w = 0 → w = 0)
    (hsep : ∀ x : UVCrossingModel W π,
      (∀ B : ℕ, x ∈ Ideal.span {const π π} ^ B) → x = 0) :
    fixedSubring π ≤ (chartHom π).range := by
  intro x hx
  obtain ⟨f, hf⟩ := chartHom_surjOn_fixedSubring hreg htwo hsep x hx
  exact RingHom.mem_range.mpr ⟨f, hf⟩

end Surjectivity
end UVCrossingModel
end
end ModularCurve
end
end P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X
