public section

open WithConv

namespace TauCeti

namespace RootsOfUnityGroup

universe u v w

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- **The inclusion `μ_n ↪ 𝔾ₘ` on points.** It is the contravariant image of the quotient
`ℤ ↠ ℤ/n` under the diagonalizable functor: precomposition with the surjection
`R[Multiplicative ℤ] ↠ R[Multiplicative (ZMod n)]` of coordinate Hopf algebras carries a
point of `μ_n = D(ℤ/n)` to a point of `𝔾ₘ = D(ℤ)`. -/
noncomputable def inclusion (n : ℕ) :
    WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A) →*
      WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A) :=
  DiagonalizableGroup.pointsMap (toMultiplicativeZMod n)

end RootsOfUnityGroup
end TauCeti
end
