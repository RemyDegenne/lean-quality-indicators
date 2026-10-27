public section

namespace TauCeti

open CartanMatrix CartanMatrix.Relations LieAlgebra

variable {B : Type*} [DecidableEq B] (R : Type*) [CommRing R] (CM : Matrix B B ℤ)

/-- The generator `Eᵢ` of `Matrix.ToLieAlgebra R CM`, the image of the free generator `Eᵢ`. -/
noncomputable def serreE (i : B) : Matrix.ToLieAlgebra R CM :=
  serreMk R CM (FreeLieAlgebra.of R (Generators.E i))

end TauCeti
end
