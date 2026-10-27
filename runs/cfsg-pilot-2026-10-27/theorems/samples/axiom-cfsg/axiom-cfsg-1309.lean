public section

namespace CFSG.Quasithin.RuType.J47

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Sporadic.Schreier.Tits

section Elements

variable {G : Type} [Group G] {F1 F2 : Subgroup G}

theorem zG_eq_hom2
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    : zG e = hom2 e ⟨titsZ, twoF4S_le_twoF4N titsZ_mem_S⟩ :=
  hom1_eq_hom2 e _ _

end Elements
end CFSG.Quasithin.RuType.J47
end
