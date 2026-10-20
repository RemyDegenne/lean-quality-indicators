public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v v' u u'

local instance {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D] :
    (CategoryTheory.Prod.fst C D).PreservesZeroMorphisms where
  map_zero _ _ := rfl

local instance {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D] :
    (CategoryTheory.Prod.snd C D).PreservesZeroMorphisms where
  map_zero _ _ := rfl

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D]

namespace ExactStructure

variable (E : ExactStructure C) (E' : ExactStructure D)

theorem isConflationExact_fst_prod :
    IsConflationExact (E.prod E') E (CategoryTheory.Prod.fst C D) :=
  ⟨fun hS => (prod_conflation_iff E E' _).1 hS |>.1⟩

end ExactStructure
end TauCeti
end
