public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126FE S126L19 S126L19a S126L20a Equiv

namespace S126L24

theorem mk_pw_mem {Ŵ : Subgroup D8} {E : ↥(coreMod 8)} (hE : (QuotientGroup.mk E : D8) ∈ Ŵ)
    (a : ZMod 2) : (QuotientGroup.mk (pw E a) : D8) ∈ Ŵ := by
  unfold pw
  split_ifs
  · rw [QuotientGroup.mk_one]
    exact Ŵ.one_mem
  · exact hE

end S126L24
end CFSG.Quasithin.H13
end
