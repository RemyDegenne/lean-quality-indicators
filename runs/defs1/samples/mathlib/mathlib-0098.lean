@[expose] public section

open scoped Pointwise

variable {R} [CommRing R] (r : R) (M : Type*) {M' M''}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M'']

namespace QuotSMulTop

open Submodule Function TensorProduct

variable {M}

/-- The action of the functor `QuotSMulTop r` on morphisms. -/
def map : (M →ₗ[R] M') →ₗ[R] QuotSMulTop r M →ₗ[R] QuotSMulTop r M' :=
  Submodule.mapQLinear _ _ ∘ₗ LinearMap.id.codRestrict _ fun _ =>
    map_le_iff_le_comap.mp <| le_of_eq_of_le (map_pointwise_smul _ _ _) <|
      smul_mono_right r le_top

end QuotSMulTop
end
