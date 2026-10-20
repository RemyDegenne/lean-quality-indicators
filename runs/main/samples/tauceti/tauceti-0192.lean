public section

noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace

open scoped AdicCompletionExtension NumberField.LiesOver

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem finprod_norm_mem_adicCompletionIntegers
    (x : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L)
    (v : HeightOneSpectrum (𝓞 K))
    (hx : ∀ w, w.under (𝓞 K) = v → x w ∈ w.adicCompletionIntegers L) :
    (∏ᶠ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Algebra.norm (v.adicCompletion K) (x w.1)) ∈ v.adicCompletionIntegers K :=
  finprod_induction _ (one_mem _) (fun _ _ ↦ mul_mem) fun w ↦
    HeightOneSpectrum.norm_mem_adicCompletionIntegers v w.1
      (hx w.1 (HeightOneSpectrum.ext w.2.over.symm))

end TauCeti.GlobalNumberFields
end
end
