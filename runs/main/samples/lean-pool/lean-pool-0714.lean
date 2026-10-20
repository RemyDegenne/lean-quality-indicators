@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory

universe u

namespace SuperCommAlgebra.Mod

variable {S : SuperCommAlgebra.{u, u}}

section Associator

variable (M N P : S.Mod.{u, u, u, u})

@[simp]
theorem assocInv_oddMap_tmulOE (m : M.odd) (w : (N.tensor P).even) :
    (assocInv M N P).oddMap (tmulOE M (N.tensor P) m w)
      = assocInvFoe M N P m w :=
  mkHom_oddMap_tmulOE (assocInvData M N P) m w

end Associator
end SuperCommAlgebra.Mod
end RS
end
