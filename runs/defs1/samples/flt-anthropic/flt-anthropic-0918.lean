set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian

namespace AlgebraicGeometry

namespace RiemannForm

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))

variable (L : RelativeGroupLaw k f)

variable (hc : L.IsCommutative)

abbrev modulePair (M : A.Modules) : Pseudofunctor.CoGrothendieck Scheme.Modules.fibration := ⟨A, M⟩

end RiemannForm
end AlgebraicGeometry
end
