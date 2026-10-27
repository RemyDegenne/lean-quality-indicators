set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian

namespace AlgebraicGeometry

def Scheme.Modules.fibration : Pseudofunctor (LocallyDiscrete (Scheme.{0}ᵒᵖ)) Cat.{0, 1} :=
  (Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁

end AlgebraicGeometry
end
