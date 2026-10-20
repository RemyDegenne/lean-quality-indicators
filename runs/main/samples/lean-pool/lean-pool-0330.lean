open Set

universe u

public noncomputable section

namespace Surreal

theorem rationalTailQuotient_abs
    (T : Set (FiniteArchimedeanClass Surreal.{u})) (x : Surreal.{u}) :
    |(Submodule.Quotient.mk x : RationalTailQuotient T)| = Submodule.Quotient.mk |x| := by
  rcases le_total 0 x with hx | hx
  · have hxq : (0 : RationalTailQuotient T) ≤ Submodule.Quotient.mk x := by
      rw [← Submodule.Quotient.mk_zero]
      exact ConvexQuotient.mk_le_mk hx
    rw [abs_of_nonneg hx, abs_of_nonneg hxq]
  · have hxq : (Submodule.Quotient.mk x : RationalTailQuotient T) ≤ 0 := by
      rw [← Submodule.Quotient.mk_zero]
      exact ConvexQuotient.mk_le_mk hx
    rw [abs_of_nonpos hx, abs_of_nonpos hxq, ← Submodule.Quotient.mk_neg]

end Surreal
end
