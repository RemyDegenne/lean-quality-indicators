namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem

set_option autoImplicit false

set_option linter.unusedTactic false

set_option linter.unreachableTactic false

set_option linter.unnecessarySeqFocus false

noncomputable section

namespace WhittakerPS2Ext

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal Matrix Topology Filter

section Main

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

variable (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))

theorem psi_ne_zero (ψ : AddChar F ℂ) (a : F) : ψ a ≠ 0 := fun h => by
  have := psi_neg_mul_self p ψ a
  rw [h, mul_zero] at this
  exact zero_ne_one this

end Main
end WhittakerPS2Ext
end
end P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem
