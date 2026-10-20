public section

noncomputable section

open Bundle Manifold Real

open scoped Manifold ContDiff

namespace TauCeti.SL2Tilde

local notation "P" => ℝ × ℝ × ℝ

local notation "Q" => WithLp 2 (ℝ × ℝ)

local notation "J" => 𝓘(ℝ, P)

local notation "K" => 𝓘(ℝ, Q)

@[simp] theorem coe_projection (p : SL2Tilde) :
    (projection p : Q) = WithLp.toLp 2 (p.x, exp p.y) := by
  exact UpperHalfSpace.coe_mk _ _

end TauCeti.SL2Tilde
end
end
