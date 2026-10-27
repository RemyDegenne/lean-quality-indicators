open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.Section8

universe u v w

public theorem exists_notation_8_14_source_data_of_typeP_bot_typeV_witness
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2') :
    ∃ R : G → Subgroup G, ∃ tildeA tildeA0 tildeA1 : Set G,
      notation_8_14_source_data M A A0 A1
        (section8DSet M A0) tildeA tildeA0 tildeA1 R := by
  rcases notation_8_10_source_typeP_witness_typeV_context_of_typeP_bot
      hPbot hNotation hWitness with
    ⟨_hUbot, _hPbot', _hV, _hMs, _hMF, _hAcentral, _hA1, hAeqA1⟩
  have hA1A : A1 ⊆ A := by
    intro x hx
    rw [hAeqA1]
    exact hx
  have hAA0 : A ⊆ A0 := by
    intro x hx
    rw [hWitness.2.2.2.1]
    exact Or.inl hx
  exact exists_mixed_notation_8_14_source_data_of_theorem_8_13
    M MF Ms A A0 A1 (by infer_instance) hNotation hA1A hAA0

end CFSG.Section8
end
