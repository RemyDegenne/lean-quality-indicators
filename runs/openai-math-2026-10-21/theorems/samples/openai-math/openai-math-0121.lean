namespace OAI

section

section

open Set MeasureTheory

open scoped ComplexConjugate RealInnerProductSpace

namespace GraphLiteralSupport

namespace Attempt4PrefixShell

open MeasureTheory Set Metric

open scoped ContDiff RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularDerivativeND_mul (A : V →L[ℝ] V) {f g : V → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : V) :
    angularDerivativeND A (fun w => f w*g w) x =
      angularDerivativeND A f x*g x + f x*angularDerivativeND A g x := by
  unfold angularDerivativeND
  change (fderiv ℝ (f*g) x) (A x) = _
  rw [fderiv_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp [mul_comm,add_comm]

end Attempt4PrefixShell
end GraphLiteralSupport
end
end
end OAI
