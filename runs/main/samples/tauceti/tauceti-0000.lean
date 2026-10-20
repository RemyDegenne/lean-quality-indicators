public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Simplicial HomologicalComplex

open TauCeti.SSet (chainComplexMap_f_comp chainComplexMap_f_comp_assoc)

universe w v u

namespace SSet

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

section EilenbergZilberTensor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]
  (K L : SSet.{w}) (R S : C)

@[simp]
lemma eilenbergZilberHomotopyEquiv_inv :
    (eilenbergZilberHomotopyEquiv K L R S).inv = shuffle K L R S :=
  (rfl)

end EilenbergZilberTensor
end SSet
end
end
