@[expose] public section

universe a w p

open CategoryTheory Opposite

open scoped Simplicial TensorProduct

namespace SSet

variable {S T U : SSet.{w}}

theorem tensorNormalizedChainComplexXMap_eq_iff (A : Type a) [AddCommGroup A]
    (f : S ⟶ T) (n : ℕ)
    (g : tensorNormalizedChainComplexX.{a, w, p} A S n ⟶
      tensorNormalizedChainComplexX.{a, w, p} A T n) :
    g = tensorNormalizedChainComplexXMap.{a, w, p} A f n ↔
      ∀ (s : S.nonDegenerate n) (x : A),
        g (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)) =
          ULift.up (T.normalizedIntegralSimplex (f.app (op ⦋n⦌) s.val) ⊗ₜ[ℤ] x) := by
  constructor
  · rintro rfl s x
    exact tensorNormalizedChainComplexXMap_single.{a, w, p} A f n s x
  · intro h
    apply tensorNormalizedChainComplexX_hom_ext.{a, w, p} A S n
    intro s x
    exact (h s x).trans (tensorNormalizedChainComplexXMap_single.{a, w, p} A f n s x).symm

end SSet
end
