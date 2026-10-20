namespace P2MW.S_MvFormalGroup_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent

set_option autoImplicit false

noncomputable section

open MvPowerSeries

universe u v w z

namespace NilYoneda

section Coefficients

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [DecidableEq σ]

theorem coeff_eq_zero_of_mem_pow {N : ℕ} {p : MvPolynomial σ R} (hp : p ∈ varIdeal R σ ^ N)
    {d : σ →₀ ℕ} (hd : d.degree < N) : MvPolynomial.coeff d p = 0 :=
  varIdeal_pow_le_lowVanish N hp d hd

end Coefficients
end NilYoneda
end
end P2MW.S_MvFormalGroup_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent
