public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {Y X : Type} [Group Y] [Group X]

theorem nonempty_equiv_sl_of_psl {n : ℕ} (h : IsPSL n 2 1 X) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact ⟨e.trans (Setup.Family.statedProjSL_equiv_of_card_two n K (by rw [hK, pow_one]))⟩

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
end
