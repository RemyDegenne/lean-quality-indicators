public section

open Function Set

namespace TauCeti.DynkinType

open RootPairing

noncomputable section

variable (n : ℕ)

theorem typeARootPermHom_typeARationalWeylGroupEquiv (hn : 1 ≤ n)
    (w : ((DynkinType.A n).rationalRootSystem (DynkinType.valid_A.mpr hn)).weylGroup) :
    typeARootPermHom n (typeARationalWeylGroupEquiv n hn w) =
      ((DynkinType.A n).rationalRootSystem (DynkinType.valid_A.mpr hn)).weylGroupToPerm w :=
  typeARootPermHom_typeAWeylGroupEquivOf n _ _ _ w

end
end TauCeti.DynkinType
end
