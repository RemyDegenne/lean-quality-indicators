namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial

open scoped BigOperators

theorem rowsSound14_1 (k : Fin GramFunctions.Block4.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form14.terms k).tag (GramFunctions.Block4.form14.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval15198 x
  · exact rowEval15199 x
  · exact rowEval15200 x
  · exact rowEval15201 x
  · exact rowEval15202 x
  · exact rowEval15203 x
  · exact rowEval15561 x
  · exact rowEval15562 x
  · exact rowEval15563 x
  · exact rowEval13629 x
  · exact rowEval13630 x
  · exact rowEval13631 x
  · exact rowEval13632 x
  · exact rowEval13633 x
  · exact rowEval13634 x
  · exact rowEval13635 x
  · exact rowEval13636 x
  · exact rowEval13637 x
  · exact rowEval15207 x
  · exact rowEval15208 x
  · exact rowEval15209 x
  · exact rowEval15210 x
  · exact rowEval15211 x
  · exact rowEval15212 x
  · exact rowEval13638 x
  · exact rowEval13639 x
  · exact rowEval13640 x
  · exact rowEval13641 x
  · exact rowEval13642 x
  · exact rowEval13643 x
  · exact rowEval15564 x
  · exact rowEval15565 x
  · exact rowEval15566 x
  · exact rowEval13656 x
  · exact rowEval13657 x
  · exact rowEval13658 x

end MUB6.Certificate.GramEntries.Block4
end OAI
