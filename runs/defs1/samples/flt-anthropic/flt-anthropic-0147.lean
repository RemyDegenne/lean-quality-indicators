set_option autoImplicit false

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

namespace LevelP

variable {A B : Type*} [CommRing A] [CommRing B] (W : WeierstrassCurve A)

def smulX (a : ℤ) (x : A) : A :=
  (W.Φ a).eval x * Ring.inverse ((W.ΨSq a).eval x)

end LevelP
end ModularCurve
end
