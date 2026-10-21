namespace OAI

namespace ContingencyTables.ForestGreedyProgram

open MatchingFPRAS.TreeTyped Polynomial FiniteGraphRootProgram WeightedArgmaxProgram

lemma polynomial_emptyGraph : PolynomialTime emptyGraphRealizer := by
  apply polynomial_composition
  · apply polynomial_boundedRange LargeEdgeCatalogProgram.polynomial_vertexCount (2*X)
    intro z
    have hr : z.1.1.1.length≤weight z := (list_length_le_weight z.1.1.1).trans
      ((weight_fst z.1.1).trans ((weight_fst z.1).trans (weight_fst z)))
    have hc : z.1.1.2.length≤weight z := (list_length_le_weight z.1.1.2).trans
      ((weight_snd z.1.1).trans ((weight_fst z.1).trans (weight_fst z)))
    simp only [LargeEdgeCatalogProgram.vertexCount,eval_mul,eval_ofNat,eval_X]
    omega
  · exact polynomial_map (polynomial_constant [])

end ContingencyTables.ForestGreedyProgram
end OAI
