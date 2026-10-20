public section

namespace TauCeti

namespace PDE

open Matrix

variable {X n : Type*} [Fintype n] [DecidableEq n]

namespace UniformlyEllipticOn

variable {Ω Ω' : Set X} {a b : X → Matrix n n ℝ}
  {lam Lam lam' Lam' : ℝ}

lemma add_bounded (h : UniformlyEllipticOn Ω a lam Lam) {b : X → Matrix n n ℝ}
    {Mu : ℝ} (hMu_nonneg : 0 ≤ Mu) (hMu_lt : Mu < lam)
    (hb_upper : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (b x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖) :
    UniformlyEllipticOn Ω (fun x => a x + b x) (lam - Mu) (Lam + Mu) := by
  refine UniformlyEllipticOn.of_bounds (sub_pos.mpr hMu_lt) ?_ (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · linarith [h.le, hMu_nonneg]
  · refine lower_bound_toQuadraticForm'_add_of_lower_bound (h.lower_bound hx) ?_ ξ
    intro ζ
    exact (neg_le_neg
      (abs_toQuadraticForm'_le_of_abs_dotProduct_mulVec_le (hb_upper hx) ζ)).trans
      (neg_abs_le ((b x).toQuadraticForm' ζ))
  · exact abs_dotProduct_add_mulVec_le (h.upper_bound hx) (hb_upper hx) η ξ

end UniformlyEllipticOn
end PDE
end TauCeti
end
