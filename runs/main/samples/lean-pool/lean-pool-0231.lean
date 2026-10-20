@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

theorem ishiiOperatorComparisonConditionOn_affineSecondOrderOperator_of_same_hessian_bound
    {C : Set (Point n)} {R : Set Real}
    {G : Point n -> Hessian n -> Real} {b : Point n -> Point n}
    {c f : Point n -> Real} {ω : Real -> Real}
    (hω : ComparisonModulus ω)
    (hG : ∀ z : Point n, z ∈ C ->
      ∀ X Y : Hessian n, Y <= X -> G z X <= G z Y)
    (hbound :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        (G y X + dotProduct (b y) (quadraticPenaltyGradientLeft α x y) +
              c y * r - f y) -
            (G x X + dotProduct (b x) (quadraticPenaltyGradientLeft α x y) +
              c x * r - f x) <=
          ω (α * ‖x - y‖ ^ 2 + ‖x - y‖)) :
    IshiiOperatorComparisonConditionOn C R (affineSecondOrderOperator G b c f) := by
  refine ⟨ω, hω, ?_⟩
  intro α hα x hx y hy r hr X Y hXY
  have hXYle : X <= Y := hXY.left_le_right
  have hGYX : G y Y <= G y X :=
    hG y hy Y X hXYle
  have hcoeff := hbound α hα x hx y hy r hr X Y hXY
  dsimp [affineSecondOrderOperator, quadraticPenaltyGradientLeft] at hcoeff ⊢
  linarith

end ViscositySolns
end
