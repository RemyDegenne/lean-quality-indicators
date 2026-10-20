@[expose] public section

namespace PiTensorProduct

open PiTensorProduct LinearMap Module TensorProduct

variable {ι : Type*}

section SemiRing

variable {R : Type*} {M : ι → Type*} [CommSemiring R] [Π i, AddCommMonoid (M i)]
  [Π i, Module R (M i)]

/-- The canonical linear map from `⨂[R] i, Dual R (M i)` to `Dual R (⨂[R] i, M i)`,
sending `⨂ₜ[R] i, f i` to the composition of `PiTensorProduct.map f` with
the linear equivalence `⨂[R] i, R →ₗ R` given by multiplication. -/
noncomputable def dualDistrib [Finite ι] : (⨂[R] i, Dual R (M i)) →ₗ[R] Dual R (⨂[R] i, M i) :=
  haveI := Fintype.ofFinite ι
  (LinearMap.compRight _ (constantBaseRingEquiv ι R).toLinearMap) ∘ₗ piTensorHomMap

end SemiRing
end PiTensorProduct
end
