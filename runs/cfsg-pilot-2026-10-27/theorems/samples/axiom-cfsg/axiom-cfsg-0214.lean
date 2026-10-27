public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section StatedSL

theorem orth_normal_pgroup_prod_eq_bot {Γ₂ Γ₃ : Type*} [Group Γ₂] [Group Γ₃] [IsSimpleGroup Γ₂]
    [IsSimpleGroup Γ₃] (h2 : ¬ IsPGroup 2 Γ₂) (h3 : ¬ IsPGroup 2 Γ₃)
    {W : Subgroup (Γ₂ × Γ₃)} [hWn : W.Normal] (hW : IsPGroup 2 ↥W) : W = ⊥ := by
  have hs1 : Function.Surjective (MonoidHom.fst Γ₂ Γ₃) := fun a => ⟨(a, 1), rfl⟩
  have hs2 : Function.Surjective (MonoidHom.snd Γ₂ Γ₃) := fun b => ⟨(1, b), rfl⟩
  haveI hn1 : (W.map (MonoidHom.fst Γ₂ Γ₃)).Normal := Subgroup.Normal.map hWn _ hs1
  haveI hn2 : (W.map (MonoidHom.snd Γ₂ Γ₃)).Normal := Subgroup.Normal.map hWn _ hs2
  have hb1 : W.map (MonoidHom.fst Γ₂ Γ₃) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.map (MonoidHom.fst Γ₂ Γ₃)) with h | h
    · exact h
    · exfalso
      have hp := orth_isPGroup_map hW (MonoidHom.fst Γ₂ Γ₃)
      rw [h] at hp
      exact h2 (hp.of_equiv Subgroup.topEquiv)
  have hb2 : W.map (MonoidHom.snd Γ₂ Γ₃) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.map (MonoidHom.snd Γ₂ Γ₃)) with h | h
    · exact h
    · exfalso
      have hp := orth_isPGroup_map hW (MonoidHom.snd Γ₂ Γ₃)
      rw [h] at hp
      exact h3 (hp.of_equiv Subgroup.topEquiv)
  rw [eq_bot_iff]
  rintro ⟨a, b⟩ hx
  have ha : a ∈ W.map (MonoidHom.fst Γ₂ Γ₃) := ⟨(a, b), hx, rfl⟩
  have hb : b ∈ W.map (MonoidHom.snd Γ₂ Γ₃) := ⟨(a, b), hx, rfl⟩
  rw [hb1, Subgroup.mem_bot] at ha
  rw [hb2, Subgroup.mem_bot] at hb
  rw [Subgroup.mem_bot]
  exact Prod.ext ha hb

end StatedSL
end CFSG.RankThree.GF2n.Smith81
end
