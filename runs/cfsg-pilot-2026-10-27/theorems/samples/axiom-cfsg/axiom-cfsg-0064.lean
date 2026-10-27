public section

namespace CFSG.EvenSporadicStandard.J4Std.Data11

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.Native

open CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs (duadMasks starMasks star_facts starOK_closure
  mem_star_lt)

theorem u0J_ne (hM : MatFacts) : u0J ≠ 1 := by
  intro h
  have h0 : eta uJ 11 u0Mask = eta uJ 11 0 := by rw [eta_zero]; exact h
  have := eta_inj hM u0Mask (by norm_num [u0Mask]) 0 (by norm_num) h0
  norm_num [u0Mask] at this

end CFSG.EvenSporadicStandard.J4Std.Data11
end
