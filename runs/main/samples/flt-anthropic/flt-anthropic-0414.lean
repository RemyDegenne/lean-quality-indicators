namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_sectionAt_eq_of_nsmulPt_eq_one

attribute [-instance] GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId

set_option autoImplicit false

universe u

p2m_open

open scoped Quaternion

namespace GLUEbc

section A

variable {K : Type u} [Field K] [IsAlgClosed K]

theorem discreteTopology_of_isFinite {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g] :
    DiscreteTopology ↥Z := by
  have h0 : DiscreteTopology ↥(Spec (CommRingCat.of K)) := ⟨Subsingleton.elim _ _⟩
  have h1 : _root_.IsDiscrete (Set.univ : Set ↥(Spec (CommRingCat.of K))) := isDiscrete_univ_iff.mpr h0
  have h2 := g.isDiscrete_preimage h1
  rw [Set.preimage_univ] at h2
  exact isDiscrete_univ_iff.mp h2

end A
end GLUEbc
end P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_sectionAt_eq_of_nsmulPt_eq_one
