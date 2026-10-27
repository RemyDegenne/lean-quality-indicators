public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.Quasithin.H13.F431.D4q.Struct CFSG.Quasithin.H13.F431.D4q.Loc

open scoped commutatorElement

section D4

set_option linter.unusedSectionVars false

theorem burnsideF4m_core12_D4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .D4tw 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    (∀ x ∈ centerOf (perfectCore M₁), x ≠ 1 → x * x = 1 → x ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) ∧
    (∀ x ∈ centerOf (perfectCore M₂), x ≠ 1 → x * x = 1 →
      GLKind.D4tw = .Sp4 ∧ x ∈ ctr (oPPrime 2 (Gp ⊓ M₂))) := by
  haveI := hyp.normal
  obtain ⟨K, fK, finK, cK, σ, hσ3, hf1, hK, hσq, Ψ, h1, h2⟩ :=
    burnsideF4m_D4_chart hyp.toHypF_4_4g
  have hc : ∀ a b : E, ⁅a, b⁆ ∈ Gp := burnsideF4m_commutator_mem_of_out hyp.centralizer_trivial
    (burnsideF4m_out_transport Ψ (burnsideF4m_D4_out_comm σ hf1 hK hσq))
  have hφ : Function.Injective (Gp.subtype.comp Ψ.toMonoidHom) :=
    Gp.subtype_injective.comp Ψ.injective
  refine ⟨burnsideF4m_core1_of_model hc _ hφ (burnsideF4m_inf_eq_map Ψ h1)
    (burnsideF4m_D4_P0_center_le σ hσ3 hf1 hK hσq), ?_⟩
  intro x hx hx1 _
  rw [burnsideF4m_centerOf_perfectCore_eq_bot_of_model hc _ hφ (burnsideF4m_inf_eq_map Ψ h2)
    (burnsideF4m_D4_P1_center_eq_bot σ hσ3 hf hK hσq)] at hx
  exact absurd (Subgroup.mem_bot.1 hx) hx1

end D4
end CFSG.ASVolI
end
