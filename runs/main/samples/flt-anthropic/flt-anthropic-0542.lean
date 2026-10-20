namespace P2MW.S_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite

set_option autoImplicit false

universe u v

section hensSplitHelpers

open IsLocalRing

theorem hensSplit_isMaximal_map_mk {S : Type v} [CommRing S] {K m : Ideal S} (hm : m.IsMaximal)
    (hK : K ≤ m) : (m.map (Ideal.Quotient.mk K)).IsMaximal := by
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective hm
    with h | h
  · exfalso
    apply hm.ne_top
    rw [← hensSplit_comap_map_mk hK, h, Ideal.comap_top]
  · exact h

end hensSplitHelpers
end P2MW.S_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
