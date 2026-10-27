set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory

open scoped NNReal

namespace LanglandsTunnell.TateLocal

open NumberField.StandardAddChar

section Std

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

def integersPositiveCompacts : TopologicalSpace.PositiveCompacts (v.adicCompletion K) where
  carrier := (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  isCompact' := isCompact_iff_compactSpace.mpr
    (show CompactSpace (v.adicCompletionIntegers K) from inferInstance)
  interior_nonempty' := by
    have h : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
      Valued.isOpen_valuationSubring _
    rw [h.interior_eq]
    exact ⟨0, (v.adicCompletionIntegers K).zero_mem⟩

end Std
end LanglandsTunnell.TateLocal
end
