public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_nqHigherThompson (R : Subgroup G) (j : ℕ) :
    R ≤ normalizer (nqHigherThompson R j : Set G) := by
  have hc : (CFSG.higherElemThompson ↥R j).Characteristic :=
    CFSG.Quasithin.SteinbergBK.higherElemThompson_characteristic j
  exact Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)

end CFSG.Quasithin.H13.NQBlock
end
