public section

open CliffordAlgebra QuadraticMap

namespace TauCeti.SpinPolarizationData

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {n : ℕ} (b : Module.Basis (Fin n) K P.W) [Invertible (2 : K)]

@[simp]
theorem typeDQuadraticEquiv_rootGenerator (hn : 4 ≤ n) (hline : P.line = ⊥)
    (k : Fin n ⊕ Fin n) :
    (P.typeDQuadraticEquiv b hline (TypeDStd.rootGenerator n hn k) : CliffordAlgebra Q) =
      match k with
      | .inl i => P.typeDSimpleRootBivector b (by omega) i
      | .inr i => P.typeDSimpleNegativeRootBivector b (by omega) i := by
  cases k with
  | inl i =>
      by_cases hi : (i : ℕ) + 1 < n
      · simpa using P.typeDQuadraticEquiv_rootGenerator_inl_of_add_one_lt b hn hline hi
      · simpa using P.typeDQuadraticEquiv_rootGenerator_inl_of_not_add_one_lt b hn hline hi
  | inr i =>
      by_cases hi : (i : ℕ) + 1 < n
      · simpa using P.typeDQuadraticEquiv_rootGenerator_inr_of_add_one_lt b hn hline hi
      · simpa using P.typeDQuadraticEquiv_rootGenerator_inr_of_not_add_one_lt b hn hline hi

end TauCeti.SpinPolarizationData
end
