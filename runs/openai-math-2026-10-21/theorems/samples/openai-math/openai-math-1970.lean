namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial

open scoped BigOperators

theorem entryCheck24_19 : entry24_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_19 k)) := by decide +kernel

end MUB6.Certificate.GramEntries.Block3
end OAI
