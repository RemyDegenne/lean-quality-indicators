public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

open scoped MatrixGroups

namespace RuDataM

variable {G : Type} [Group G] (M : RuDataM G)

variable [Finite G]

theorem Q5_inf_W :
    M.Q5 M.b5el_mem_H ⊓ M.W = M.Q5 M.b5el_mem_H ⊓ ruS M.L :=
  le_antisymm (inf_le_inf_left _ M.W_le_S) (le_inf inf_le_left M.Q5_inf_S_le_W)

end RuDataM
end CFSG.Quasithin.RuType
end
