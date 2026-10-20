set_option autoImplicit false

noncomputable section

universe u v w w'

namespace TwoChartCech

namespace Mumford

variable {R : Type u} [CommRing R]

variable {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

variable (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]

def quot : (Fin (rank d) → R) →ₗ[R] (C1 ⧸ LinearMap.range d) :=
  (Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)).choose_spec.choose

end Mumford
end TwoChartCech
end
