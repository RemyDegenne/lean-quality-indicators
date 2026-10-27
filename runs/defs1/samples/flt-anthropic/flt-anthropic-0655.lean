namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex

set_option autoImplicit false

set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian TopologicalSpace

noncomputable section

universe u

namespace P2mIdentityComponent

section Law

variable {k : Type u} [Field k] [IsAlgClosed k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f)

local notation "pt" => 𝟙 (Spec (CommRingCat.of k))

def onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) : SchemeHomOver t (f₀ L) :=
  liftPt L (L.one t) (range_one_subset L t)

end Law
end P2mIdentityComponent
end
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
