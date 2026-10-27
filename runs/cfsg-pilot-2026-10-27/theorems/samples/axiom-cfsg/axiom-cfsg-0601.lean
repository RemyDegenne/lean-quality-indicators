public section

namespace CFSG.QuasithinUnique.Bridge.Over

namespace A7

open scoped commutatorElement

open Equiv CFSG.QuasithinUnique.Unc25K1.Six CFSG.Assembly.LowTwoRank

open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.A312L.Seven CFSG.QuasithinUnique.Unc25G2.A312Sub

theorem Concl.of_map {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {B : Subgroup X}
    (h : Concl (B.map e.toMonoidHom)) : Concl B := by
  rcases h with h | h | h
  · obtain ⟨f⟩ : Nonempty (↥(B.map e.toMonoidHom) ≃* alternatingGroup (Fin 5)) := h
    exact Or.inl ⟨(mapEquiv e B).symm.trans f⟩
  · exact Or.inr (Or.inl (IsPSL.of_mulEquiv (mapEquiv e B) h))
  · obtain ⟨f⟩ : Nonempty (↥(B.map e.toMonoidHom) ≃* alternatingGroup (Fin 6)) := h
    exact Or.inr (Or.inr ⟨(mapEquiv e B).symm.trans f⟩)

end A7
end CFSG.QuasithinUnique.Bridge.Over
end
