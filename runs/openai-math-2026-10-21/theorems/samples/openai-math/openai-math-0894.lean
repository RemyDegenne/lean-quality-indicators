namespace OAI

namespace CriticalHoneycomb.Transfer.YangBaxter

open scoped BigOperators

section Algebra

variable (C A S x y z w ii : ℂ)

variable (hC : C = (2*S+1)*A) (hA : A^2 = (1-S)/2)
  (hS : S^2 = 1/2) (hy : y^2+x^2=1) (hw : w^2+z^2=1) (hi : ii^2+1=0)

lemma component_011010 :
    leftComponent C A S x y z w ii 0 1 1 0 1 0 =
    rightComponent C A S x y z w ii 0 1 1 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 0 1 0 (by decide)]

end Algebra
end CriticalHoneycomb.Transfer.YangBaxter
end OAI
