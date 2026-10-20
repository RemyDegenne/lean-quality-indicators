public section

open Module Real

open scoped ComplexConjugate unitInterval

namespace TauCeti

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace TotallyRealPath

variable {E}

@[simp]
theorem map_apply (Λ : TotallyRealPath E) (B : I → E ≃L[ℂ] E)
    (hB : Continuous fun t => (B t : E →L[ℂ] E)) (t : I) :
    Λ.map B hB t = (Λ t).map (((B t).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ) :=
  (rfl)

end TotallyRealPath
end TauCeti
end
