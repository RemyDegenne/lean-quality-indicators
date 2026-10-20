namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_extraLevel_forall_factorsThrough_iff

set_option autoImplicit false

p2m_open

open scoped Quaternion

universe u

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace GLUEgrp

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

theorem nsmulPt_one_pt (n : ℕ) : nsmulPt L t n (L.one t) = L.one t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [nsmulPt]; rw [ih, L.one_mul]

end GLUEgrp
end P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_extraLevel_forall_factorsThrough_iff
