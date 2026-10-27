public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace ModuliProblem

variable {B : Scheme.{u}} (P Q : ModuliProblem B) {X Y : EllObj B}

/-- The **fibre** of a moduli problem `𝒫` over an object `X = (E/S)` of `Ell/B`: the functor
`T ↦ 𝒫(E_T/T)` on schemes over `S`, where `E_T` is the base change of `E` along `T ⟶ S`. -/
@[expose, simps!]
noncomputable def fibre (X : EllObj B) : (Over X.base)ᵒᵖ ⥤ Type (u + 1) :=
  X.baseChangeFunctor.op ⋙ P

end ModuliProblem
end TauCeti.AlgebraicGeometry
end
