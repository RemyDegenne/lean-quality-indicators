namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial

open scoped BigOperators

theorem entryCheck8_1 : entry8_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form8.terms k).coefficient) (rows8_1 k)) := by decide +kernel

end MUB6.Certificate.GramEntries.Block1
end OAI
