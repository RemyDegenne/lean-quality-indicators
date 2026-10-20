namespace P2MW.S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 6400000

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

section

p2m_reactivate

section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

section

p2m_reactivate

section

p2m_reactivate

section

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

section

p2m_reactivate

section

p2m_reactivate

section

p2m_reactivate

section

@[expose] public section

p2m_reactivate

p2m_reactivate

section

p2m_open

p2m_reactivate

section

p2m_open

p2m_open_scoped

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

section

p2m_reactivate

section

p2m_reactivate

section

p2m_reactivate

section

noncomputable section

p2m_open

open scoped Polynomial.Bivariate

p2m_reactivate

section

p2m_open

p2m_open_scoped

p2m_reactivate

section

p2m_open

p2m_open_scoped

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

section

@[expose] public section

p2m_reactivate

section

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

p2m_open

p2m_open_scoped

p2m_reactivate

p2m_reactivate

section

@[expose] public section

p2m_reactivate

section

p2m_open

p2m_open_scoped

noncomputable section

namespace WeierstrassCurve

namespace Affine

p2m_open

p2m_open

universe u

variable {F : Type u} [Field F]

p2m_reactivate

section GenericPointGroup

variable {W : Affine F}

local notation "ι" => algebraMap F W.FunctionField

def mapPoint (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) : (W.map ι).toAffine.Point :=
  Affine.Point.some (ι a) (ι b) (nonsingular_map_algebraMap hΔ hA)

end GenericPointGroup
end Affine
end WeierstrassCurve
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end P2MW.S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet
