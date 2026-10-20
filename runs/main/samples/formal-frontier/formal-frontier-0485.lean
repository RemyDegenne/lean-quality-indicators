@[expose] public section

universe a w p r v

open CategoryTheory Limits Opposite

open scoped Simplicial TensorProduct

namespace SSet

@[simp]
theorem tensorNormalizedChainComplexXIso_inv_ι (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (n : ℕ) (s : S.nonDegenerate n) (x : A) :
    (tensorNormalizedChainComplexXIso.{a, w, p} A S n).inv
        (S.ιNormalizedChainComplex (R := ModuleCat.of ℤ (ULift.{max w p} A)) s.val (ULift.up x)) =
      ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x) := by
  rw [← tensorNormalizedChainComplexXIso_hom_single.{a, w, p} A S n s x]
  exact ModuleCat.inv_hom_apply _ _

end SSet
end
