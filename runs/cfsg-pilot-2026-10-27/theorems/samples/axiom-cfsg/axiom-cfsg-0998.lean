public section

namespace CFSG.Quasithin.GoldMLB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.GoldMLA

open CFSG.RankThreeCoreUniqueness.Helpers

open scoped commutatorElement

variable {G : Type} [Group G]

theorem leviCent_le (P : Subgroup G) : leviCent P ≤ P := fun _ hg => hg.1

end CFSG.Quasithin.GoldMLB
end
