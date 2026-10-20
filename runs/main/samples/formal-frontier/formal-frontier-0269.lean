@[expose] public section

open Function

universe u v

namespace ProfiniteGrp

@[simp]
theorem primewisePadicKernelIdealContinuousMulEquiv_symm_apply
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T2Space Y]
    (f : primewisePadic.{u} →ₜ* Y) (hf : Surjective f)
    (x : primewisePadicRing.{u}) :
    (primewisePadicKernelIdealContinuousMulEquiv f hf).symm
      (f (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x))) =
      Multiplicative.ofAdd
        (Ideal.Quotient.mk (primewisePadicKernelIdeal f) x) := by
  apply (primewisePadicKernelIdealContinuousMulEquiv f hf).symm_apply_eq.mpr
  exact (primewisePadicKernelIdealContinuousMulEquiv_mk f hf x).symm

end ProfiniteGrp
end
