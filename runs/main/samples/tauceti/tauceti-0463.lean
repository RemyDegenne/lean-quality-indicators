public section

noncomputable section

open Bundle Manifold Real

open scoped Manifold ContDiff

namespace TauCeti.SL2Tilde

local notation "P" => ℝ × ℝ × ℝ

local notation "Q" => WithLp 2 (ℝ × ℝ)

local notation "J" => 𝓘(ℝ, P)

local notation "K" => 𝓘(ℝ, Q)

@[simp] theorem projection_eq_projection_iff (p q : SL2Tilde) :
    projection p = projection q ↔ p.x = q.x ∧ p.y = q.y := by
  constructor
  · intro h
    have hx := congrArg (fun r : UpperHalfSpace ℝ => (r : Q).fst) h
    have hy := congrArg UpperHalfSpace.height h
    exact ⟨by simpa using hx, exp_injective (by simpa using hy)⟩
  · rintro ⟨hx, hy⟩
    apply UpperHalfSpace.ext_fst_height <;> simp [hx, hy]

end TauCeti.SL2Tilde
end
end
