namespace P2MW.S_IsLocalRing_exists_hull_of_forall_pullback_surjective_of_tangent_injective

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

universe u

namespace P2mSchlessingerHull

open IsLocalRing

variable {O : Type u} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
  (S : Datum O)

section adm

variable (O) (d : ℕ)

variable {O d}

scoped instance (J : Adm O d) : Nontrivial (Q O d J) := Ideal.Quotient.nontrivial_iff.2 (ne_top J)

scoped instance (J : Adm O d) : IsLocalRing (Q O d J) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk J.I) Ideal.Quotient.mk_surjective

scoped instance (J : Adm O d) : IsArtinianRing (Q O d J) :=
  (isArtinianRing_iff_isNilpotent_maximalIdeal _).2 ⟨J.N, by
    rw [maximalIdeal_quotient J.I J.le, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker,
      Ideal.mk_ker]
    exact J.pow_le⟩

abbrev fac {K J : Adm O d} (h : K.I ≤ J.I) : Q O d K →ₐ[O] Q O d J := Ideal.Quotient.factorₐ O h

end adm
end P2mSchlessingerHull
end
end P2MW.S_IsLocalRing_exists_hull_of_forall_pullback_surjective_of_tangent_injective
