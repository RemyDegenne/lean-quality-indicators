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

namespace Datum

variable (d : ℕ)

variable {S d}

variable (S)

scoped instance : Nontrivial S.Rh := Ideal.Quotient.nontrivial_iff.2 fun h =>
  (IsLocalRing.maximalIdeal.isMaximal (PS O S.dm)).ne_top (top_le_iff.1 (h ▸ S.Jinf_le_max))

scoped instance : IsLocalRing S.Rh := IsLocalRing.of_surjective' (Ideal.Quotient.mk S.Jinf) Ideal.Quotient.mk_surjective

scoped instance : IsAdicComplete (maximalIdeal S.Rh) S.Rh := by
  rw [maximalIdeal_Rh]; exact IsLocalRing.isAdicComplete_map_maximalIdeal_quotient S.Jinf

def resR : S.Rh →+* ResidueField O :=
  Ideal.Quotient.lift S.Jinf (resS O S.dm) fun a ha => by
    have := S.Jinf_le_max ha; rwa [← ker_resS] at this

end Datum
end P2mSchlessingerHull
end
end P2MW.S_IsLocalRing_exists_hull_of_forall_pullback_surjective_of_tangent_injective
