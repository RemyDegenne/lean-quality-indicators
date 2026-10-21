namespace OAI

namespace CriticalHoneycomb.Transfer.YangBaxter

open scoped BigOperators

section Algebra

variable (C A S x y z w ii : ℂ)

variable (hC : C = (2*S+1)*A) (hA : A^2 = (1-S)/2)
  (hS : S^2 = 1/2) (hy : y^2+x^2=1) (hw : w^2+z^2=1) (hi : ii^2+1=0)

include hi in
lemma reduce_101020_5 :
    poly_101020_3 C A S x y z w ii =
    poly_101020_5 C A S x y z w ii := by
  have hq := congrArg (fun t : ℂ => (poly_101020_6 C A S x y z w ii) * t) hi
  dsimp only [poly_101020_3, poly_101020_5, poly_101020_6, complexAdd, complexMul, complexPow] at hq ⊢
  linear_combination hq

end Algebra
end CriticalHoneycomb.Transfer.YangBaxter
end OAI
