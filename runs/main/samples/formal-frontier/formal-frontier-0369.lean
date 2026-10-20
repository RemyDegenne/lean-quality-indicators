@[expose] public section

universe a w p

open CategoryTheory Opposite

open scoped Simplicial TensorProduct

namespace SSet

variable {S T U : SSet.{w}}

@[simp]
theorem tensorNormalizedChainNatIso_inv_app (A : Type a) [AddCommGroup A] (S : SSet.{w}) :
    (tensorNormalizedChainNatIso.{a, w, p} A).inv.app S =
      (tensorNormalizedChainIso.{a, w, p} A S).inv := rfl

end SSet
end
