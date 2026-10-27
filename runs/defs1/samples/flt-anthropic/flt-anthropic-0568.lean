set_option autoImplicit false

universe u v w

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

namespace LevelP

section Borel

variable (p : ℕ) (a : ℕ)

def borelData : LevelPData (BorelRing p a) := (univData p).map (BorelRing.ofUniv p a)

end Borel
end LevelP
end ModularCurve
end
