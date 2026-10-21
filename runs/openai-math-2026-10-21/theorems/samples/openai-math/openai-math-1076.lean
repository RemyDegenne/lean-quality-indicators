namespace OAI

noncomputable section

open scoped ComplexOrder

namespace HochschildCentralQuantization

open BoundedHochschild HochschildDixmier HochschildSakai HochschildRigidity

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma centerPart_trace (a z : M) (hz : ∀ x : M, Commute z x) :
    τ (z*centerPart e τ hτ htr hfaith a)=τ (z*a) :=
  (exists_unique_center_part e τ hτ htr hfaith a).choose_spec.2.2 z hz

end HochschildCentralQuantization
end
end OAI
