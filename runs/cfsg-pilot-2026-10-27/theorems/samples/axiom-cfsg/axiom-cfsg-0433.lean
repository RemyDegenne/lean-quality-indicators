public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.OutStructure

open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)

open CFSG.HardMathSupport.Curtis.NaturalModuleCensus

section Generic

theorem perfectJoinHub_of_torusFree_classical {P : TauCeti.LieTypeIndex → Prop}
    (hP : P = IdxA ∨ P = IdxTwistedA ∨ P = IdxB ∨ P = IdxD ∨ P = IdxTwistedD) {X : Type}
    [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hX : IsLieOfTorusFree P p X) :
    PerfectJoinHub p X := by
  obtain ⟨d, hPd, ht, ⟨e⟩⟩ := hX
  obtain ⟨hd, hG2⟩ := ToralCensus.classical_index hP hPd
  exact perfectJoinHub_of_classicalIndex d hd hG2 e hp hp5 ht

end Generic
end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc
end
