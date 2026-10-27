public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L1547

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {W : Type*} [CommGroup W]

namespace ModData

variable {A S P : Subgroup (MulAut W)} {I : Finset (Subgroup (MulAut W))} {z₀ : W}

theorem card_L (h : ModData A S P I z₀) {L : Subgroup (MulAut W)} (hL : L ∈ I) :
    Nat.card L = 6 := by
  obtain ⟨e, -, -⟩ := h.nat L hL
  rw [Nat.card_congr e.toEquiv, card_SL2]

end ModData
end L1547
end CFSG.Quasithin.EmptyFaithfulMultiple
end
