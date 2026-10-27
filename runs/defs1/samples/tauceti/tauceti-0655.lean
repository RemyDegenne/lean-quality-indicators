public section

noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace

open scoped NNReal

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

section NormQuotient

open IdeleClassGroup

/-- **The idele class group splits as `C_K¹ × ℝ>0`.** The infinite place `w` determines the
isomorphism of topological groups sending an idele class `c` to its norm-one part
`c · s(‖c‖)⁻¹` and its norm `‖c‖`, where `s = ideleClassNormSection K w`. -/
def normOneProdEquiv (w : InfinitePlace K) :
    IdeleClassGroup (𝓞 K) K ≃ₜ* normOne K × ℝ≥0ˣ :=
  -- The hypotheses are stated before use: unifying them inside the application has to match
  -- the commutative-group instance of `IdeleClassGroup` with the quotient group instance.
  let f : IdeleClassGroup (𝓞 K) K →ₜ* ℝ≥0ˣ := .mk ideleClassNorm continuous_ideleClassNorm
  have hs : Function.RightInverse (ideleClassNormSection K w) f :=
    ideleClassNorm_ideleClassNormSection w
  have hN (c : IdeleClassGroup (𝓞 K) K) : c ∈ normOne K ↔ f c = 1 := mem_normOne_iff
  ContinuousMulEquiv.kerProdOfRightInverse (G := IdeleClassGroup (𝓞 K) K) (H := ℝ≥0ˣ) f
    (ideleClassNormSection K w) hs hN

end NormQuotient
end TauCeti.GlobalNumberFields
end
end
