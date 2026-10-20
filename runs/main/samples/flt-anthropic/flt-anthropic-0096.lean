namespace P2MW.S_MvFormalGroup_exists_map_eq_and_existsUnique_hom_of_pullback_of_surjective

set_option autoImplicit false

noncomputable section

open MvPowerSeries

universe u

namespace P2mFGGlue

section LawApp

variable {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}

theorem lawApp_apply {τ : Type} (L : Fin n → MvPowerSeries (Fin n ⊕ Fin n) R)
    (a b : Fin n → MvPowerSeries τ R) (k : Fin n) :
    lawApp L a b k = subst (Sum.elim a b) (L k) := rfl

end LawApp
end P2mFGGlue
end
end P2MW.S_MvFormalGroup_exists_map_eq_and_existsUnique_hom_of_pullback_of_surjective
