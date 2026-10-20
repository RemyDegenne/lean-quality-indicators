namespace P2MW.S_HopfAlgebra_comul_finitePartIdempotent_mul

set_option maxHeartbeats 1600000

open scoped TensorProduct

open IsLocalRing

section Antipode

open IsLocalRing HopfAlgebra

variable {R : Type*} [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

p2m_reactivate

variable [IsLocalRing R]

theorem FinitePart.antipode_eq_self {e : H} (he : IsIdempotentElem e)
    (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (maximalIdeal R) = ⊤) :
    HopfAlgebraStruct.antipode R e = e := by
  let S : H →ₐ[R] H := FinitePart.antipodeAlgHom
  have hS : Function.Surjective S := FinitePart.antipode_surjective
  have h1 : Module.Finite R (Localization.Away (S e)) := FinitePart.finite_away_map S hS he hfin
  have h2 : Ideal.map (algebraMap R (Localization.Away (1 - S e))) (maximalIdeal R) = ⊤ := by
    have := FinitePart.map_maximalIdeal_away_map S (1 - e) hgen
    rwa [map_sub, map_one] at this
  exact FinitePart.finitePartIdempotent_unique _ _ (he.map S) he h1 hfin h2 hgen

end Antipode
end P2MW.S_HopfAlgebra_comul_finitePartIdempotent_mul
