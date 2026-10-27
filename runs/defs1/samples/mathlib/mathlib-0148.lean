@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Choose a partial isomorphism witnessing that `X` and `Y` are birational over `S`. -/
noncomputable def BirationalOver.partialIso {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    (h : BirationalOver sX sY) :=
  h.choose

end AlgebraicGeometry.Scheme
end
