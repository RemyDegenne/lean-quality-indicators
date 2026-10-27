public section

namespace CFSG.ComponentClassification.SolMax.Spor516

open CFSG CFSG.Blueprint CFSG.ComponentClassification.GSThmB

open CFSG.Sporadic.FischerOddCore
  (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven)

theorem leafAt_Fi24Prime
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .Fi24Prime) :
    CF516LeafAt S :=
  leafAt_of_filter e CatalogueU.sporadicOddCoreFree_Fi24Prime (N := 1255205709190661721292800)
    (fun _ => by
      rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .Fi24Prime) =
        Nat.card NativeSporadic.Fi24prime from rfl, Sporadic.Fi24.card_Fi24prime])
    [(2, 21), (3, 16), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1)]
    (by decide) (by decide) (Qs := {3}) (by decide)
    (fun _ q hq t ht B hB => by
      rw [Finset.mem_singleton] at hq
      subst hq
      rw [(CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven e t ht
        B hB).1]
      norm_num)

end CFSG.ComponentClassification.SolMax.Spor516
end
