namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial

open scoped BigOperators

theorem rowsSound7_6 (k : Fin GramFunctions.Block5.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form7.terms k).tag (GramFunctions.Block5.form7.terms k).charge GramFunctions.Block5.form6) x := by
  fin_cases k
  · exact rowEval19199 x
  · exact rowEval19200 x
  · exact rowEval19201 x
  · exact rowEval19202 x
  · exact rowEval19203 x
  · exact rowEval19204 x
  · exact rowEval19205 x
  · exact rowEval19206 x
  · exact rowEval19207 x
  · exact rowEval19208 x
  · exact rowEval19209 x
  · exact rowEval19210 x
  · exact rowEval19211 x
  · exact rowEval19212 x
  · exact rowEval19213 x
  · exact rowEval19214 x
  · exact rowEval19215 x
  · exact rowEval19216 x
  · exact rowEval19217 x
  · exact rowEval19218 x

end MUB6.Certificate.GramEntries.Block5
end OAI
