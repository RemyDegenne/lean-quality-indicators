public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

variable {ρ : Representation (ZMod 2) G V}

theorem false_of_pCore_sup_zpowers_eq_bot
    [Finite G] [Finite V]
    (hρ : Function.Injective ρ)
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    (hH : hP ρ = ⊤) (IH : HasFactors148Below (Nat.card G))
    (hinner : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      ¬ ∀ g : G, ∃ l ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ g u = ρ l u)
    {N : Subgroup G} {a : G} (hN : N.Normal) (hN1 : N ≠ ⊥)
    (hcompl : IsCompl (commOn ρ N ⊤) (fixSub ρ N)) (ha2 : a * a = 1)
    (hfa : ∀ n ∈ N, (∀ x ∈ commOn ρ N ⊤, ρ n x = x) → n = 1)
    (hact : ∀ g : G, ∃ h ∈ N ⊔ Subgroup.zpowers a, ∀ x ∈ commOn ρ N ⊤, ρ g x = ρ h x)
    (hout : ∀ n ∈ N, ¬ ∀ x ∈ commOn ρ N ⊤, ρ a x = ρ n x)
    (hNE : ∀ X : Subgroup G, IsElemAbelian 2 X → NoExcess ρ X (commOn ρ N ⊤))
    (hO₀ : CFSG.pCore 2 ↥(cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a) = ⊥) : False := by
  have hW : ∀ g : G, ∀ w ∈ fixSub ρ N, ρ g w ∈ fixSub ρ N := fun g w hw =>
    rep_apply_mem_fixSub_of_normal ρ hN g hw
  obtain ⟨m, Hs, hD, hF⟩ := hasFactors148_sup_zpowers hρ hshape hH IH hN hN1 hcompl.sup_eq_top
    ha2 hfa hact hout hO₀
  have hnc := not_isComponentOf_sup_zpowers hρ hH hshape hinner hN hcompl.sup_eq_top
    (sup_sup_zpowers_eq_top hact) hD
  exact false_of_card_fixSub_subRep_le hH hN hW hcompl ha2 hfa hact hout hNE fun X hX =>
    card_mul_card_fixSub_le_of_isFactor148
      (injective_subRep_sup_zpowers hρ hN hW hcompl.sup_eq_top ha2 hO₀)
      (fun L hL => allowed_shape_sup_zpowers (cenOn_commOn_normal hN) hshape hL)
      (hP_subRep_sup_zpowers_eq_top hρ hH hN hW ha2 hfa hact hout) hD hF hnc hX

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
end
