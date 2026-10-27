namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_forall_factorsThrough_iff_iff_of_translate_corr_of_isAlgClosed_heightNormalised_eq_oneLeg

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField

open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace G3C3

p2m_open

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]

noncomputable def comapExtraLevel {E E' : FakeEllipticCurve Λ N S} (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (hvia : IsoVia E E' i hi)
    {ℓ : ℕ} (C' : E'.ExtraLevel ℓ) : E.ExtraLevel ℓ where
  K := C'.K
  levK := C'.levK ≫ i.inv
  levK_closed := by haveI := C'.levK_closed; infer_instance
  levK_sub := by
    intro T t P Q hP hQ
    rw [factorsThrough_comp_inv_iff i hi] at hP hQ
    constructor
    · rw [factorsThrough_comp_inv_iff i hi, hvia.1 t]; exact (C'.levK_sub t _ _ hP hQ).1
    · rw [factorsThrough_comp_inv_iff i hi, mapPt_inv i hi hvia]; exact (C'.levK_sub t _ _ hP hQ).2
  levK_one := by
    intro T t
    rw [factorsThrough_comp_inv_iff i hi, mapPt_one i hi hvia]; exact C'.levK_one t
  levK_torsion := by
    intro T t P hP
    rw [factorsThrough_comp_inv_iff i hi] at hP
    apply mapPt_injective i hi
    rw [mapPt_nsmulPt i hi hvia, mapPt_one i hi hvia]
    exact C'.levK_torsion t _ hP
  levK_stable := by
    intro x T t P hP
    rw [factorsThrough_comp_inv_iff i hi] at hP ⊢
    rw [mapPt_pushPt_act i hi hvia]
    exact C'.levK_stable x t _ hP
  levK_disjoint := by
    intro T t P hP hlev
    rw [factorsThrough_comp_inv_iff i hi] at hP
    apply mapPt_injective i hi
    rw [mapPt_one i hi hvia]
    exact C'.levK_disjoint t _ hP ((hvia.2.2 t P).1 hlev)
  levK_finite := by
    have h : (C'.levK ≫ i.inv) ≫ E.f = C'.levK ≫ E'.f := by rw [Category.assoc, inv_comp_f i hi]
    rw [h]; exact C'.levK_finite
  levK_flat := by
    have h : (C'.levK ≫ i.inv) ≫ E.f = C'.levK ≫ E'.f := by rw [Category.assoc, inv_comp_f i hi]
    rw [h]; exact C'.levK_flat
  levK_finitePresentation := by
    have h : (C'.levK ≫ i.inv) ≫ E.f = C'.levK ≫ E'.f := by rw [Category.assoc, inv_comp_f i hi]
    rw [h]; exact C'.levK_finitePresentation
  levK_rank := by
    have h : (C'.levK ≫ i.inv) ≫ E.f = C'.levK ≫ E'.f := by rw [Category.assoc, inv_comp_f i hi]
    rw [h]; exact C'.levK_rank
  levK_fibre := by
    intro k _ _ sk hℓ
    obtain ⟨e', he'⟩ := C'.levK_fibre k sk hℓ
    let τ : {P : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough (C'.levK ≫ i.inv) P} ≃
        {P' : SchemeHomOver (geomPoint k sk) E'.f // FactorsThrough C'.levK P'} :=
      { toFun := fun P => ⟨mapPt i.hom hi P.1, (factorsThrough_comp_inv_iff i hi C'.levK P.1).1 P.2⟩
        invFun := fun P' => ⟨mapPt i.inv (inv_comp_f i hi) P'.1, by
          rw [factorsThrough_comp_inv_iff i hi, mapPt_inv_hom]; exact P'.2⟩
        left_inv := fun P => Subtype.ext (mapPt_hom_inv i hi P.1)
        right_inv := fun P' => Subtype.ext (mapPt_inv_hom i hi P'.1) }
    refine ⟨e'.trans τ.symm, fun x y => ?_⟩
    show mapPt i.inv (inv_comp_f i hi) (e' (x + y) : SchemeHomOver (geomPoint k sk) E'.f) =
      E.L.mul (geomPoint k sk) (mapPt i.inv (inv_comp_f i hi) (e' x)) (mapPt i.inv (inv_comp_f i hi) (e' y))
    rw [he', mapPt_mul_inv i hi hvia]

end G3C3
end P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_forall_factorsThrough_iff_iff_of_translate_corr_of_isAlgClosed_heightNormalised_eq_oneLeg
