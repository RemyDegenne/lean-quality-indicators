public section

namespace TauCeti.continuousZModDual

variable {p : ℕ} [Fact p.Prime] {k : ℕ}

theorem padicInt_apply_eq_toZModPow_mul_eval_one
    (χ : continuousZModDual (p ^ k) (Multiplicative ℤ_[p])) (x : ℤ_[p]) :
    Multiplicative.toAdd (χ.toMul (Multiplicative.ofAdd x)) =
      PadicInt.toZModPow k x * evalₗ (Multiplicative.ofAdd (1 : ℤ_[p])) χ := by
  let φ : ℤ_[p] →ₜ+ ZMod (p ^ k) :=
    ⟨χ.toMul.toMonoidHom.toAdditive,
      continuous_toAdd.comp (χ.toMul.continuous.comp continuous_ofAdd)⟩
  rw [evalₗ_apply]
  exact φ.padicInt_apply_eq_toZModPow_mul_apply_one x

end TauCeti.continuousZModDual
end
