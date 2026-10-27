public section

namespace CFSG.Quasithin.C48Spor

open CFSG.Open hiding StatedSL StatedSp

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

open scoped commutatorElement

variable {G : Type} [Group G]

theorem K_le_sporX {H K : Subgroup G} (hK : K ≤ H) : K ≤ sporX H K :=
  le_sporX hK Subgroup.le_normalizer

end CFSG.Quasithin.C48Spor
end
