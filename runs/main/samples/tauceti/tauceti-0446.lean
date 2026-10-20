public section

open Module

namespace TauCeti.IntegralLattice

universe u v w x y z

variable {V : Type u} {W : Type v}

variable [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

@[simp]
theorem coe_orthogonalSumCarrierEquiv_snd (L : IntegralLattice V) (M : IntegralLattice W)
    (p : L.orthogonalSum M) : ((orthogonalSumCarrierEquiv L M p).2 : W) = p.1.2 := by
  simp [orthogonalSumCarrierEquiv]

end TauCeti.IntegralLattice
end
