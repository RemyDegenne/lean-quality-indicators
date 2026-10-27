public section

open Polynomial

namespace TauCeti

variable (R : Type*) [CommRing R]

namespace LegendreRing

section lift

variable {R} {S : Type*} [CommRing S] [Algebra R S]

/-- The **universal property** of the Legendre line: an element `x` of an `R`-algebra `S` such that
`x` and `x - 1` are units determines an `R`-algebra map sending `λ` to `x`. -/
noncomputable def lift (x : S) (hx : IsUnit x) (hx₁ : IsUnit (x - 1)) :
    LegendreRing R →ₐ[R] S :=
  AdjoinRoot.liftAlgHom (legendreRelation R)
    (aeval ((x ^ 2 - x + 1) ^ 3 * ↑(hx.mul hx₁).unit⁻¹ ^ 2)) x (by
      have h := (hx.mul hx₁).mul_val_inv
      simp only [legendreRelation, eval₂_sub, eval₂_pow, eval₂_add, eval₂_mul, eval₂_X,
        eval₂_one, eval₂_C, AlgHom.coe_toRingHom, aeval_X]
      linear_combination (-(x ^ 2 - x + 1) ^ 3 * (x * (x - 1) * ↑(hx.mul hx₁).unit⁻¹ + 1)) * h)

end lift
end LegendreRing
end TauCeti
end
