public section

namespace CFSG.RankThree.PartOne.OutStructure

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Ree
  CFSG.ComponentClassification.UnbalancedCatalog

theorem outPNice_F4_odd
    {p r f : ℕ}
    (hp : p.Prime) (hr2 : r ≠ 2) {X : Type} [Group X]
    (h : ChevalleyExceptionalModel X .F4 r f) : OutPNice p X := by
  obtain ⟨⟨hrp, hf1, -⟩, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hm
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form hrp hr2 hf1 K hK .F4 (Or.inl rfl)
  have hcard := card_ringAut_and_isCyclic hrp K hK
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcard.1]; omega)
  have := hcard.2
  exact OutPNice.of_mulEquiv e (outPNice_of_hom_cyclic hp Θ hker)

end CFSG.RankThree.PartOne.OutStructure
end
