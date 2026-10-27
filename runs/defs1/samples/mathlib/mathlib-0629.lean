@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- `X` and `Y` are birational over `S` if there exists a partial isomorphism between them
that is compatible with the structure maps to `S`. -/
def BirationalOver {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) : Prop :=
  ∃ f : PartialIso X Y, f.IsOver sX sY

end AlgebraicGeometry.Scheme
end
