public section

namespace CFSG.QuasithinUnique.L246A7

open Equiv CFSG.Open

local notation "S₇" => Equiv.Perm (Fin 7)

local notation "A₇" => alternatingGroup (Fin 7)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (D : Alt7Data L)

variable {T : Subgroup G}

omit [Finite G] in
theorem sup_le_normalizer (hTN : T ≤ Subgroup.normalizer (L : Set G)) :
    L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTN

end CFSG.QuasithinUnique.L246A7
end
