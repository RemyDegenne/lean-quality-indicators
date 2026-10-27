public section

namespace CFSG.Quasithin.F53.Stellmacher.S43

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod Equiv

open CFSG.LieType.BorelTits

open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

open scoped commutatorElement

variable {G : Type} [Group G]

theorem map_oTwoRes_eq_alt [Finite G] {X : Subgroup G} {ψ : ↥X →* Perm (Fin 5)}
    (hψ : Function.Surjective ψ) :
    ((oTwoRes X).subgroupOf X).map ψ = alternatingGroup (Fin 5) :=
  le_antisymm (map_oTwoRes_le_alt ψ) (alt_le_map_oTwoRes hψ)

end CFSG.Quasithin.F53.Stellmacher.S43
end
