namespace P2MW.S_CerednikDrinfeld_QM_trace_eq_of_smooth_of_isCommutative_of_forall_injective_trace_eq

set_option autoImplicit false

set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

open MvPowerSeries

open scoped Quaternion

universe u

noncomputable section

namespace TraceClosedBody

section Dual

variable (k : Type u) [Field k]

scoped instance isAdicComplete_Jε : IsAdicComplete (Jε k) (DualNumber k) :=
  isAdicComplete_of_isNilpotent _ (isNilpotent_Jε k)

scoped instance isIso_specMap_qJc : IsIso (Spec.map (qJc k)) := by
  have h : qJc k = (quotJ k).toCommRingCatIso.hom := by rw [RingEquiv.toCommRingCatIso_hom]; rfl
  rw [h]
  infer_instance

abbrev mkS (C : Type u) [CommRing C] (J : Ideal C) : Spec (CommRingCat.of (C ⧸ J)) ⟶ Spec (CommRingCat.of C) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))

end Dual
end TraceClosedBody
end
end P2MW.S_CerednikDrinfeld_QM_trace_eq_of_smooth_of_isCommutative_of_forall_injective_trace_eq
