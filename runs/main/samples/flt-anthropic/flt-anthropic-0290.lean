namespace P2MW.S_CerednikDrinfeld_CosetGraph_awayUnits_meetOrder_eq_inf_map_conj_of_finiteAdeleEvalAt_eq

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open scoped TensorProduct Quaternion NumberField Pointwise

open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

namespace CSTowerT21

namespace Stab

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

local notation "ev" w => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w

theorem not_mem_of_prime_ne {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hne : ℓ ≠ p) {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
  intro hℓv
  rw [← natGenerator_dvd_iff'] at hv hℓv
  have h1 := (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hp).mp hv
  have h2 := (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hℓ).mp hℓv
  exact hne (h2.symm.trans h1)

end Stab
end CSTowerT21
end P2MW.S_CerednikDrinfeld_CosetGraph_awayUnits_meetOrder_eq_inf_map_conj_of_finiteAdeleEvalAt_eq
