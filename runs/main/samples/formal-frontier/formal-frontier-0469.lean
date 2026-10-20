@[expose] public section

universe a w p r v

open CategoryTheory Limits Opposite

open scoped Simplicial TensorProduct

namespace SSet

@[simp]
theorem tensorNormalizedChainComplex_d (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (i j : ℕ) :
    (tensorNormalizedChainComplex.{a, w, p} A S).d i j =
      tensorNormalizedDifferential.{a, w, p} A S i j := rfl

end SSet
end
