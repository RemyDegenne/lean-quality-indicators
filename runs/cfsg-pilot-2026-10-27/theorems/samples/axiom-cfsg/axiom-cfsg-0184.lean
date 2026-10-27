public section

namespace CFSG.Quasithin.LieOver

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Blueprint.Chevalley

open CFSG.LieType.Chevalley CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.B113Lie

theorem asLieTwoAt_e6 :
    AsLieTwoAt .E6 := by
  intro n f X _ _ _ _ hmod
  exact lb_sylowProps Tag.E6 (by decide) (hmod.chevalleyExceptionalModel (by decide)).2

end CFSG.Quasithin.LieOver
end
