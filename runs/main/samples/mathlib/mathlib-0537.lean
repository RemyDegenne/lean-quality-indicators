@[expose] public section

variable {ι α β : Type*}

open Set Function

open scoped Pointwise

namespace Ring

variable {R : Type*} [CommSemiring R]

theorem not_isField_iff_exists_ideal_bot_lt_and_lt_top [Nontrivial R] :
    ¬IsField R ↔ ∃ I : Ideal R, ⊥ < I ∧ I < ⊤ := by
  refine ⟨fun h ↦ ?_, fun ⟨I, h_bot, h_top⟩ ↦ not_isField_of_ne_of_ne h_bot.ne' h_top.ne⟩
  obtain ⟨I, hI, hIm⟩ := exists_maximal_of_not_isField h
  exact ⟨I, bot_lt_iff_ne_bot.mpr hI, lt_top_iff_ne_top.mpr hIm.ne_top⟩

end Ring
end
