namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain

open scoped TensorProduct

noncomputable section

namespace P2mLocalIndex

section Residue

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
  (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)

variable (c : w.1.adicCompletion L) (hcO : c ∈ w.1.adicCompletionIntegers L)

def cV : kv K v ⊗[v.adicCompletionIntegers K] w.1.adicCompletionIntegers L :=
  (1 : kv K v) ⊗ₜ (⟨c, hcO⟩ : w.1.adicCompletionIntegers L)

end Residue
end P2mLocalIndex
end
end P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one
