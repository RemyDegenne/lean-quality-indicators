@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject

open CategoryTheory.Preadditive CategoryTheory.Category CategoryTheory.Idempotents

open Opposite

open scoped Simplicial

noncomputable section

namespace AlgebraicTopology

namespace AlternatingFaceMapComplex

variable {C : Type*} [Category* C] [Preadditive C]

variable (X : SimplicialObject C)

variable (Y : SimplicialObject C)

/-- The alternating face map complex, on objects -/
@[implicit_reducible]
def obj : ChainComplex C ℕ :=
  ChainComplex.of (fun n => X _⦋n⦌) (objD X) (d_squared X)

end AlternatingFaceMapComplex
end AlgebraicTopology
end
end
