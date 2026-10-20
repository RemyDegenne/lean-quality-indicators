@[expose] public section

universe a w p r v

open CategoryTheory Limits Opposite

open scoped Simplicial TensorProduct

namespace SSet

theorem tensorNormalizedChainIso_eq_iff (A : Type a) [AddCommGroup A]
    (S : SSet.{w})
    (e : tensorNormalizedChainComplex.{a, w, p} A S ≅
      S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))) :
    e = tensorNormalizedChainIso.{a, w, p} A S ↔ ∀ (n : ℕ) (s : S.nonDegenerate n) (x : A),
      e.hom.f n (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)) =
        S.ιNormalizedChainComplex (R := ModuleCat.of ℤ (ULift.{max w p} A)) s.val (ULift.up x) := by
  constructor
  · rintro rfl n s x
    exact tensorNormalizedChainComplexXIso_hom_single.{a, w, p} A S n s x
  · intro h
    apply Iso.ext
    ext n : 1
    apply tensorNormalizedChainComplex_hom_ext.{a, w, p} A S n
    intro s x
    exact (h n s x).trans (tensorNormalizedChainComplexXIso_hom_single.{a, w, p} A S n s x).symm

end SSet
end
