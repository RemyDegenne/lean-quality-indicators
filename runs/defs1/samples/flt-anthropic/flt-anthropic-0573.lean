namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

open NeronModelInfra (SchemeHomOver)

universe u

noncomputable section

namespace GoodReductionJacobian

p2m_open

namespace RelativeGroupLaw

p2m_open

namespace ClosedSubmonoidC2

section Subscheme

open AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}

scoped instance isReduced_redSub (Z : Closeds G) : IsReduced (redSub Z) :=
  (AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker Z).1

variable (L : RelativeGroupLaw k f) (Z : Closeds G)

def mulMap : pullback (redι Z ≫ f) (redι Z ≫ f) ⟶ G :=
  (L.mul (pullback.fst (redι Z ≫ f) (redι Z ≫ f) ≫ redι Z ≫ f)
    ⟨pullback.fst _ _ ≫ redι Z, by simp only [Category.assoc]⟩
    ⟨pullback.snd _ _ ≫ redι Z, by simpa using pullback.condition.symm⟩).1

end Subscheme
end ClosedSubmonoidC2
end RelativeGroupLaw
end GoodReductionJacobian
end
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem
