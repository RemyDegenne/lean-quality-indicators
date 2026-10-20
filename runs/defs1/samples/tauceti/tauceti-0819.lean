public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

variable (μ : R)

/-- The points `P = (x₁, y₁)` and `Q = (x₂, y₂)` form a **basis of the `3`-torsion** of `W` in every
fibre, over a ring in which `3` is a unit: they lie on `W`, the `3`-division polynomial `Ψ₃`
vanishes at both, the `2`-division polynomial `ψ₂ = 2Y + a₁X + a₃` is a unit at both, and
`x₂ - x₁` is a unit. Over a field these say that `P` and `Q` have order `3` and that `Q` is not
`±P`. -/
structure IsThreeTorsionBasis (W : WeierstrassCurve R) (x₁ y₁ x₂ y₂ : R) : Prop where
  /-- `3` is a unit. -/
  isUnit_three : IsUnit (3 : R)
  /-- `P` lies on `W`. -/
  equation_fst : W.toAffine.Equation x₁ y₁
  /-- `Q` lies on `W`. -/
  equation_snd : W.toAffine.Equation x₂ y₂
  /-- `Ψ₃` vanishes at `P`. -/
  eval_Ψ₃_fst : W.Ψ₃.eval x₁ = 0
  /-- `Ψ₃` vanishes at `Q`. -/
  eval_Ψ₃_snd : W.Ψ₃.eval x₂ = 0
  /-- `ψ₂` is a unit at `P`. -/
  isUnit_ψ₂_fst : IsUnit (W.ψ₂.evalEval x₁ y₁)
  /-- `ψ₂` is a unit at `Q`. -/
  isUnit_ψ₂_snd : IsUnit (W.ψ₂.evalEval x₂ y₂)
  /-- The `x`-coordinates of `P` and `Q` differ by a unit. -/
  isUnit_sub : IsUnit (x₂ - x₁)

end WeierstrassCurve
end
