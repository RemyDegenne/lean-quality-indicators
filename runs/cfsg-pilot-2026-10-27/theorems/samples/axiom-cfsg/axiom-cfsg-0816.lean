public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs

section L823Div

theorem card_le_two_of_inf_eq_bot_l3 {V : Type} [CommGroup V] [Finite V]
    {L M : Subgroup (MulAut V)} (hLM : Mathieu.IsOver L M) {n : ℕ} (hn : 1 ≤ n)
    (hL : BinaryNineTensor L ⊤ ⊥ n) {E : Subgroup (MulAut V)} (hEM : E ≤ M)
    (hEe : IsElemAbelian2 E) (hEL : E ⊓ L = ⊥) : Nat.card E ≤ 2 := by
  obtain ⟨K, _, _, _, hK, e, hLe, hMN⟩ := exists_model_l3nine hLM hL
  rw [← card_map_congrHom e E]
  refine L3Nine.card_le_two_of_inf_img_eq_bot hn hK ((Subgroup.map_mono hEM).trans hMN)
    ((isElemAbelian2_map_congrHom e).2 hEe) ?_
  have h := Subgroup.map_inf_eq E L (congrHom e) (congrHom_injective e)
  rw [hEL, Subgroup.map_bot] at h
  rw [← hLe]
  exact h.symm

end L823Div
end CFSG.Quasithin.H13
end
