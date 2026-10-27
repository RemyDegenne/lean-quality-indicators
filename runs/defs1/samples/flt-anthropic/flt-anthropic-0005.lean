namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit

universe u

p2m_open

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

p2m_open

namespace FrameBridge

open Opposite TopologicalSpace

variable {X : Scheme.{u}}

section restrict

variable (W : X.Opens)

abbrev secX (W' : (W : Scheme.{u}).Opens) (a : Γ(W, W')) : Γ(X, W.ι ''ᵁ W') := a

end restrict
end FrameBridge
end Modules
end Scheme
end AlgebraicGeometry
end
end P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
