@[expose] public section

noncomputable section

universe u v

namespace Module.Basis

variable {R : Type u} [CommRing R]

variable {M : Type v} [AddCommGroup M] [Module R M]

variable {n : ℕ} (b : Basis (Fin n) R M)

@[simp]
theorem topExteriorEquiv_wedge :
    b.topExteriorEquiv b.topExteriorWedge = 1 :=
  b.topExteriorCoordinate_wedge

end Module.Basis
end
end
