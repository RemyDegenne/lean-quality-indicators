namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial

open scoped BigOperators

theorem entryCheck19_12 : entry19_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form19.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form19.terms k).coefficient) (rows19_12 k)) := by decide +kernel

end MUB6.Certificate.GramEntries.Block3
end OAI
