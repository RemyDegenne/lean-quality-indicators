@[expose] public section

noncomputable section

universe u v

namespace Module.Basis

variable {R : Type u} [CommRing R]

variable {M : Type v} [AddCommGroup M] [Module R M]

variable {n : ℕ} (b : Basis (Fin n) R M)

/-- A basis indexed by `Fin n` identifies its `n`th exterior power with the ring. -/
def topExteriorEquiv : (⋀[R]^n M) ≃ₗ[R] R :=
  LinearEquiv.ofLinearMap b.topExteriorCoordinate b.topExteriorInverse
    b.topExteriorCoordinate_comp_inverse b.topExteriorInverse_comp_coordinate

end Module.Basis
end
end
