public section

namespace TauCeti.FiniteQuadraticModule

universe u v

section Pi

variable {ι : Type v} [Fintype ι] (A : ι → FiniteQuadraticModule.{u})

/-- **The orthogonal sum of a finite family of finite quadratic modules**: the group `Π i, A i`
with the quadratic map `x ↦ ∑ i, q_i(x_i)`, Mathlib's `QuadraticMap.pi`, and its polar pairing.

Reducible, exactly as `TauCeti.FiniteQuadraticModule.prod` is, so that the carrier of an orthogonal
sum reduces to the product of the carriers. -/
abbrev pi : FiniteQuadraticModule.{max u v} where
  carrier := ∀ i, A i
  pairing := LinearMap.toAddMonoidHom'.comp
    (QuadraticMap.pi fun i ↦ (A i).quadratic).polarBilin.toAddMonoidHom
  pairing_comm x y := QuadraticMap.polar_comm _ x y
  quadratic := QuadraticMap.pi fun i ↦ (A i).quadratic
  polar_eq_pairing' _ _ := rfl

end Pi
end TauCeti.FiniteQuadraticModule
end
