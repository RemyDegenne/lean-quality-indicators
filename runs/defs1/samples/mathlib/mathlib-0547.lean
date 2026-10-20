@[expose] public section

open Simplicial CategoryTheory Limits Opposite

universe w

namespace SSetPair

section

variable (C : Type*) [Category* C] [HasCoproducts.{w} C] [Preadditive C]

variable {C} (P P' P'' : SSetPair.{w}) (f : P ⟶ P') (g : P' ⟶ P'') (R : C)

/--
Given a pair of simplicial sets `i : X ⟶ Y` (with `i` a monomorphism)
and `R : C` (e.g. `C := Ab` and `R := ℤ`), this is the cokernel cofork
expressing the chain complex `SSetPair.chainComplex` of the pair
as a cokernel of the map `X.chainComplex R ⟶ Y.chainComplex R`.
-/
noncomputable def cokernelCoforkChainComplex :
    CokernelCofork (SSet.chainComplexMap P.hom R) :=
  CokernelCofork.ofπ _ (chainComplex_condition ..)

end
end SSetPair
end
