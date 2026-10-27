public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley
  CFSG.RankThree.CentralCover TableB TableBSymp

open NbrInnerRest

section Exc

variable {K : Type} [Field K]

theorem ggTorusNbr_E8 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusNbr p 8 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) :=
  ggTorusNbr_of_secElt hp (TableBExc.idImage_subset_inn_E8 K)
    (TableBExc.center_recipeGroup_eq_bot .E8 K)
    (ggTorusSecElt_of_mulEquiv (TableBExc.recipeEquiv .E8 K)
      (ggTorusSecElt_of_reflElt hp hp2 (ggTorusReflElt_adjoint (τ := .E8) hp hpq
        (TableBExc.isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E8
          (Nat.coprime_one_left p))
        (cartanE_connected (by decide)) (fun i j h => cartanE_entry_ne_zero hp hp2 i j h)
        (TableBExc.card_torusPow_E8 hp hpq)
        (IOneRest.ggExcToralRankInput_E7E8 (Or.inr rfl) hp hp2 hpq))))

end Exc
end CFSG.StandardType
end
