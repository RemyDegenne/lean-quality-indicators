@[expose] public section

open Simplicial CategoryTheory Limits Opposite

universe w

namespace SSetPair

section

variable (C : Type*) [Category* C] [HasCoproducts.{w} C] [Preadditive C]

variable {C} (P P' P'' : SSetPair.{w}) (f : P ⟶ P') (g : P' ⟶ P'') (R : C)

variable {P P'} in
/-- The morphism of relative simplicial chain complexes induces by a morphism
of pairs of simplicial sets. -/
noncomputable abbrev chainComplexMap : P.chainComplex R ⟶ P'.chainComplex R :=
  ((SSetPair.chainComplexFunctor C).obj R).map f

end
end SSetPair
end
