namespace P2MW.S_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open NeronModelInfra (SchemeHomOver)

namespace GoodReductionJacobian

p2m_open

namespace PartialAction

p2m_open

namespace MilneL43

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)}

section Equality

variable (L : RelativeGroupLaw k f) (a : PartialAction k f p)

abbrev OD : Scheme.{u} := (Dset L a : (O a).Opens)

end Equality
end MilneL43
end PartialAction
end GoodReductionJacobian
end
end P2MW.S_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal
