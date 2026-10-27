public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups

open CFSG.GH74.Exceptional CFSG.LieType.Multipliers

open scoped Matrix

local notation "P45" => Equiv.Perm (Fin 45)

local notation "Q45" => QP45.originalSubgroup

local notation "A45" => QA45.originalSubgroup

local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)

theorem fpow_inv (b : C2) : (fpow b)⁻¹ = fpow b := by
  cases b <;> simp [fpow, f45_inv]

end CFSG.RankThree.GF2n.Parrott
end
