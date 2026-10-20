public section

noncomputable section

open UpperHalfPlane

open scoped OnePoint

namespace TauCeti.UpperHalfPlane

/-- A point of `ℍ ∪ ∂ℍ` other than `∞`, as a complex number of nonnegative imaginary part: a
point of `ℍ` is itself and a real ideal point `x` is `x`. The value at `∞` is `0`
(`toComplex_inr_infty`), and carries no meaning. -/
def toComplex : ℍ ⊕ OnePoint ℝ → ℂ :=
  Sum.elim (↑) fun ξ ↦ ((OnePoint.elim ξ 0 id : ℝ) : ℂ)

end TauCeti.UpperHalfPlane
end
end
