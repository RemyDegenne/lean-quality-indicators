namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_iso_of_stdIsoPackage

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

open H2C in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}
    {R : Type} [CommRing R] {L : Type} [CommRing L] [Algebra R L]
    (u w : FakeEllipticCurve.WithFullLevel Λ N m R)
    (e : pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≅ pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (e_snd : e.hom ≫ pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) = pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (e_mul : ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of L)) (x y : SchemeHomOver t (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))),
      ((u.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mul t x y).1 ≫ e.hom =
        ((w.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mul t
          ⟨x.1 ≫ e.hom, by rw [Category.assoc, e_snd, x.2]⟩ ⟨y.1 ≫ e.hom, by rw [Category.assoc, e_snd, y.2]⟩).1)
    (e_act : ∀ x : ↥Λ,
      pullback.lift (pullback.fst u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.act x) (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
          (by rw [Category.assoc, u.1.act_over x, pullback.condition]) ≫ e.hom =
        e.hom ≫ pullback.lift (pullback.fst w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.act x) (pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
          (by rw [Category.assoc, w.1.act_over x, pullback.condition]))
    (e_P : pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ (u.2.P).1) (𝟙 _)
          (by rw [Category.assoc, (u.2.P).2, Category.comp_id, Category.id_comp]) ≫ e.hom =
        pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ (w.2.P).1) (𝟙 _)
          (by rw [Category.assoc, (w.2.P).2, Category.comp_id, Category.id_comp]))
    (e_lev : ∃ c : pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
        c ≫ pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) =
          pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) ≫ e.hom)
    (e_lev' : ∃ c' : pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
        c' ≫ pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) =
          pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) ≫ e.inv) :
    ∃ (uL wL : FakeEllipticCurve.WithFullLevel Λ N m L),
      FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap R L) u uL ∧
      FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap R L) w wL ∧
      FakeEllipticCurve.WithFullLevel.Iso uL wL := by
  obtain ⟨c, hc⟩ := e_lev
  obtain ⟨c', hc'⟩ := e_lev'

  obtain ⟨uL, gu, hgu, umul, uact, ulev, ulev', uP⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff (algebraMap R L) u
  obtain ⟨wL, gw, hgw, wmul, wact, wlev, wlev', wP⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff (algebraMap R L) w
  refine ⟨uL, wL, ⟨gu, hgu, umul, uact, ulev, uP⟩, ⟨gw, hgw, wmul, wact, wlev, wP⟩, ?_⟩

  obtain ⟨κu, κu₁, κu₂, κu₃, κu₄⟩ : ∃ κu : uL.1.A ≅ pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))),
      κu.hom ≫ pullback.fst _ _ = gu ∧ κu.hom ≫ pullback.snd _ _ = uL.1.f ∧
      κu.inv ≫ gu = pullback.fst _ _ ∧ κu.inv ≫ uL.1.f = pullback.snd _ _ :=
    ⟨hgu.isoPullback, hgu.isoPullback_hom_fst, hgu.isoPullback_hom_snd, hgu.isoPullback_inv_fst, hgu.isoPullback_inv_snd⟩
  obtain ⟨κw, κw₁, κw₂, κw₃, κw₄⟩ : ∃ κw : wL.1.A ≅ pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))),
      κw.hom ≫ pullback.fst _ _ = gw ∧ κw.hom ≫ pullback.snd _ _ = wL.1.f ∧
      κw.inv ≫ gw = pullback.fst _ _ ∧ κw.inv ≫ wL.1.f = pullback.snd _ _ :=
    ⟨hgw.isoPullback, hgw.isoPullback_hom_fst, hgw.isoPullback_hom_snd, hgw.isoPullback_inv_fst, hgw.isoPullback_inv_snd⟩
  obtain ⟨E, Ehom, Einv⟩ : ∃ E : uL.1.A ≅ wL.1.A,
      E.hom = κu.hom ≫ e.hom ≫ κw.inv ∧ E.inv = κw.hom ≫ e.inv ≫ κu.inv :=
    ⟨κu ≪≫ e ≪≫ κw.symm, rfl, by simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]⟩
  have hE : E.hom ≫ wL.1.f = uL.1.f := by
    rw [Ehom, Category.assoc, Category.assoc, κw₄, e_snd, κu₂]
  have hEκ : E.hom ≫ κw.hom = κu.hom ≫ e.hom := by
    rw [Ehom, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hEg : E.hom ≫ gw = κu.hom ≫ e.hom ≫ pullback.fst _ _ := by
    rw [Ehom, Category.assoc, Category.assoc, κw₃]
  refine ⟨E, hE, ?_, ?_, ?_, ?_⟩
  ·
    intro T t P Q
    apply Subtype.ext
    rw [mapPt_coe, ← cancel_mono κw.hom, Category.assoc, hEκ]
    have h1 := mul_transport (algebraMap R L) u.1 uL.1 gu hgu.w κu.hom κu₁ κu₂ umul t P Q
    have h3 := mul_transport (algebraMap R L) w.1 wL.1 gw hgw.w κw.hom κw₁ κw₂ wmul t (mapPt E.hom hE P) (mapPt E.hom hE Q)
    rw [← Category.assoc, h1, e_mul, h3]
    congr 2 <;> exact Subtype.ext (by simp only [mapPt_coe, Category.assoc, hEκ])
  ·
    intro x
    have hu1 := act_transport (algebraMap R L) u.1 uL.1 gu κu.hom κu₁ κu₂ x (uact x)
    have hw1 := act_transport (algebraMap R L) w.1 wL.1 gw κw.hom κw₁ κw₂ x (wact x)
    rw [← cancel_mono κw.hom, Category.assoc, hEκ, Category.assoc, ← hw1, ← Category.assoc E.hom, hEκ, Category.assoc,
      ← e_act, ← Category.assoc κu.hom, hu1, Category.assoc]
  ·
    intro T t P
    constructor
    · intro hP
      obtain ⟨P₀, hP₀⟩ := ulev t P hP
      have hr : P₀ ≫ u.1.lev ≫ u.1.f = t ≫ Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
        rw [← Category.assoc, hP₀, Category.assoc, hgu.w, ← Category.assoc, P.2]
      let r := pullback.lift P₀ t hr
      have hrj : r ≫ pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.lev)
            (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) = P.1 ≫ κu.hom := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hP₀, Category.assoc, κu₁]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.assoc, κu₂, P.2]
      apply wlev' t (mapPt E.hom hE P)
      refine ⟨r ≫ c ≫ pullback.fst _ _, ?_⟩
      have hc1 := hc =≫ pullback.fst w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L)))
      simp only [Category.assoc, pullback.lift_fst] at hc1
      rw [mapPt_coe, Category.assoc, Category.assoc, hc1, ← Category.assoc r, hrj, Category.assoc, Category.assoc, hEg]
    · intro hP
      obtain ⟨Q₀, hQ₀⟩ := wlev t (mapPt E.hom hE P) hP
      rw [mapPt_coe] at hQ₀
      have hr : Q₀ ≫ w.1.lev ≫ w.1.f = t ≫ Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
        rw [← Category.assoc, hQ₀, Category.assoc, Category.assoc, hgw.w, ← Category.assoc E.hom, hE, ← Category.assoc, P.2]
      let r := pullback.lift Q₀ t hr
      have hrj : r ≫ pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.lev)
            (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) = P.1 ≫ κu.hom ≫ e.hom := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hQ₀, Category.assoc, hEg,
            Category.assoc, Category.assoc]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.assoc, Category.assoc, e_snd, κu₂, P.2]
      apply ulev' t P
      refine ⟨r ≫ c' ≫ pullback.fst _ _, ?_⟩
      have hc1 := hc' =≫ pullback.fst u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L)))
      simp only [Category.assoc, pullback.lift_fst] at hc1
      rw [Category.assoc, Category.assoc, hc1, ← Category.assoc r, hrj, ← κu₁]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
  ·
    apply Subtype.ext
    have hu1 := P_transport (algebraMap R L) u uL gu κu.hom κu₁ κu₂ uP
    have hw1 := P_transport (algebraMap R L) w wL gw κw.hom κw₁ κw₂ wP
    rw [mapPt_coe, ← cancel_mono κw.hom, Category.assoc, hEκ, hw1, ← e_P, ← hu1, Category.assoc]

end P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_iso_of_stdIsoPackage
