public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace ModuliProblem

variable {B : Scheme.{u}} (P Q : ModuliProblem B) {X Y : EllObj B}

namespace RelRepData

variable {P Q} (D : P.RelRepData)

/-- Along an arrow `f : X ⟶ Y` of `Ell/B`, the base change of the representing scheme over `Y`
along `f.base` represents the fibre of the problem over `X`. -/
noncomputable def representableByPullback (f : X ⟶ Y) :
    (P.fibre X).RepresentableBy ((Over.pullback f.base).obj (D.rep Y)) :=
  Functor.RepresentableBy.ofIso
    { homEquiv := ((Over.mapPullbackAdj f.base).homEquiv _ _).symm.trans
        (D.representableBy Y).homEquiv
      homEquiv_comp g h := by
        simp [Adjunction.homEquiv_naturality_left_symm, (D.representableBy Y).homEquiv_comp] }
    (P.fibreIso f).symm

end RelRepData
end ModuliProblem
end TauCeti.AlgebraicGeometry
end
