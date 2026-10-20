@[expose] public section

open Function

universe u v

namespace ProfiniteGrp

/-- A surjective primewise map identifies its target with the product
model of the exponent ideal of its kernel. -/
noncomputable def primewisePadicContinuousMulEquivModel
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T2Space Y]
    (f : primewisePadic.{u} →ₜ* Y) (hf : Surjective f) :
    Y ≃ₜ* Multiplicative (primewisePadicQuotientModel
      (primewisePadicKernelExponents f)) :=
  ((primewisePadicKernelIdealContinuousMulEquiv f hf).symm.trans
    (Ideal.quotientContinuousAddEquivOfEq
      (primewisePadicKernelIdeal_eq_idealOfExponents f)).toMultiplicative).trans
    (primewisePadicQuotientContinuousAddEquivModel
      (primewisePadicKernelExponents f)).toMultiplicative

end ProfiniteGrp
end
