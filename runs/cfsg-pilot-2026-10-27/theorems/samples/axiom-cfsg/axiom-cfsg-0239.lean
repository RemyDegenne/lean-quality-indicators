public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.F7

theorem exists_ne_of_one_lt {Ω : Type} [Fintype Ω] (hn : 1 < Fintype.card Ω) :
    ∃ i j : Ω, i ≠ j := Fintype.exists_pair_of_one_lt_card hn

end CFSG.Quasithin.Background.Harris.R1
end
