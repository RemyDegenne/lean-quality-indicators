public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected.AschTight

open scoped MatrixGroups

set_option linter.unusedSectionVars false

namespace TwinConnT

variable {G : Type} [Group G] [Finite G]

theorem oddCore_eq_bot_of_map {X : Subgroup G} {C : Subgroup X} {D : Subgroup G}
    (h : C.map X.subtype = D) (hD : classicalInvolutionOddCore ↥D = ⊥) :
    classicalInvolutionOddCore ↥C = ⊥ := by
  subst h
  let e : ↥C ≃* ↥(C.map X.subtype) := C.equivMapOfInjective X.subtype X.subtype_injective
  have hO : (classicalInvolutionOddCore ↥C).map e.toMonoidHom =
      classicalInvolutionOddCore ↥(C.map X.subtype) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  rw [hD] at hO
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hO

end TwinConnT
end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
end
