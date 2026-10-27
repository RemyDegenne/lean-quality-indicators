namespace P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le

attribute [-instance] ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

p2m_open

p2m_open_scoped

p2m_open_scoped

set_option linter.unusedSectionVars false

namespace NumberField

namespace LevelArith

namespace N5

p2m_open

section Pullback

variable (S : Finset Nat.Primes) (L F F'' : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ ↥F] [Normal ℚ ↥F'']

noncomputable def ψmap (hFF'' : F ≤ F'') : Rep.res (πmap L F F'' hFF'') ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
    (sUnitsMaxRep S L).quotientToInvariants (F''.fixingSubgroup.comap L.fixingSubgroup.subtype) :=
  Rep.ofHom ⟨Submodule.inclusion (invariants_mono S L F F'' hFF''), fun g => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    refine LinearMap.ext fun z => Subtype.ext ?_
    rfl⟩

end Pullback
end N5
end LevelArith
end NumberField
end P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le
