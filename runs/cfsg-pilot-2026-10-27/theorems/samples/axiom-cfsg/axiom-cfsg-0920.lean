public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

theorem stmt6_1_6_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4) (h614 : Stmt6_1_4_F4)
    (h615 : Stmt6_1_5_F4) : Stmt6_1_6_F4 := fun _ _ _ _ _ _ _ _ h =>
  ⟨(h.lemma_6_1_6_one_two_F4 h331 h432 h512 h614 h615).1,
    (h.lemma_6_1_6_one_two_F4 h331 h432 h512 h614 h615).2,
    h.lemma_6_1_6_three_F4 h331 h432 h512 h614 h615⟩

end CFSG.Quasithin.H13
end
