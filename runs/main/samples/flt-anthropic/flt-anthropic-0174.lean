set_option autoImplicit false

universe u v w

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

namespace LevelP

section Torus

variable (p : ℕ) (a b : ℕ)

theorem equation_torusQ_Q :
    (torusQCurve p a b).toAffine.Equation (TorusQRing.xQ p a b) (TorusQRing.yQ p a b) := by
  have h := equation_map (AdjoinRoot.of ((torusQuadratic p a).map (algebraMap _ (BorelQRing p b))))
    (equation_borelQ p b)
  rw [borelQCurve, WeierstrassCurve.map_map] at h
  exact h

end Torus
end LevelP
end ModularCurve
end
