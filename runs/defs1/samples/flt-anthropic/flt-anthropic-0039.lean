namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq

attribute [-instance] GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField

p2m_open

universe u

namespace CerednikDrinfeld

namespace QM

namespace EnumAux

p2m_open

p2m_open

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {k : Type} [Field k]

noncomputable scoped instance ptAdd (E : FakeEllipticCurve Λ N k) : Add (Pt E) := ⟨fun P Q => E.L.mul (𝟙 (Spec (CommRingCat.of k))) P Q⟩

noncomputable scoped instance ptZero (E : FakeEllipticCurve Λ N k) : Zero (Pt E) := ⟨E.L.one (𝟙 (Spec (CommRingCat.of k)))⟩

noncomputable scoped instance ptNeg (E : FakeEllipticCurve Λ N k) : Neg (Pt E) := ⟨fun P => E.L.inv (𝟙 (Spec (CommRingCat.of k))) P⟩

noncomputable scoped instance ptGroup (E : FakeEllipticCurve Λ N k) : AddCommGroup (Pt E) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := E.L.mul_assoc (𝟙 (Spec (CommRingCat.of k)))
  zero_add := E.L.one_mul (𝟙 (Spec (CommRingCat.of k)))
  add_zero := E.L.mul_one (𝟙 (Spec (CommRingCat.of k)))
  neg_add_cancel := E.L.inv_mul_cancel (𝟙 (Spec (CommRingCat.of k)))
  add_comm P Q := E.comm (𝟙 (Spec (CommRingCat.of k))) P Q

section Basic

variable (E : FakeEllipticCurve Λ N k)

noncomputable def basePt (hΛ : QuaternionAlgebra.IsOrder Λ) (P₀ : Pt E) : ↥(orbit E P₀) :=
  ⟨P₀, (mem_orbit_iff E P₀ P₀).2 ⟨⟨1, hΛ.one_mem⟩, (actPt_one E hΛ.one_mem P₀).symm⟩⟩

end Basic
end EnumAux
end QM
end CerednikDrinfeld
end P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq
