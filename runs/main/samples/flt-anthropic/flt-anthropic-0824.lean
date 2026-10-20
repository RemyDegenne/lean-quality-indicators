namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_sub_oext_ores_mem_of_od_eq_zero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

open AltOrdAux AlgebraicGeometry.Scheme.OrderedAffineCover

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (c : F.ocochain K n) (hc : F.od K n c = 0) :
    c - F.oext K n (F.ores K n c) ∈
      (show Submodule R (F.ocochain K n) from
        match n with
        | 0 => ⊥
        | m + 1 => LinearMap.range (F.od K m)) := by
  classical
  cases n with
  | zero =>

    change c - F.oext K 0 (F.ores K 0 c) ∈ (⊥ : Submodule R (F.ocochain K 0))
    rw [Submodule.mem_bot, sub_eq_zero]
    funext t
    haveI : Subsingleton (Fin (0 + 1)) := by change Subsingleton (Fin 1); infer_instance
    have hinj : Function.Injective t := fun a b _ => Subsingleton.elim a b
    have hsort : Tuple.sort t = 1 := Equiv.ext fun i => Subsingleton.elim _ _
    rw [F.oext_apply_of_injective K 0 _ t hinj, hsort, Equiv.Perm.sign_one, Units.val_one, one_smul, F.ores_apply]
    symm
    apply res_eq_self F K c t
    rw [K.osort_val, hsort]
    rfl
  | succ m =>
    change c - F.oext K (m + 1) (F.ores K (m + 1) c) ∈ LinearMap.range (F.od K m)
    refine ⟨F.ohtpy K m c, ?_⟩
    funext σ
    rw [F.od_apply]

    have hface : ∀ j : Fin (m + 2), F.res (K.ointer_le_ointer_oface σ j) (F.ohtpy K m c (K.oface σ j)) =
        F.opair K σ (m + 1) c (K.ohom m (K.oface σ j)) := by
      intro j
      rw [F.ohtpy_apply]
      exact F.res_opair K σ (K.oface σ j) (oSub_oface K σ j) (m + 1) c (K.ohom m (K.oface σ j))
        (fun u hu => K.oSub_of_mem_support_ohom m (K.oface σ j) u hu)
    simp only [hface]

    have hsum : ∑ j : Fin (m + 2), ((-1 : ℤ) ^ (j : ℕ)) • F.opair K σ (m + 1) c (K.ohom m (K.oface σ j)) =
        F.opair K σ (m + 1) c (K.olin m (K.ohom m) (K.obd m (Finsupp.single σ 1))) := by
      rw [K.obd_single, map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, map_zsmul, K.olin_single]
    rw [hsum]

    have hH := K.obd_ohom_add_ohom_obd m σ
    rw [← eq_sub_iff_add_eq'] at hH
    rw [hH, map_sub, map_sub, opair_single_of_oSub F K σ (m + 1) c σ (K.oSub_refl σ), F.res_refl_apply,
      F.opair_oesort_single K σ (m + 1) c σ (K.oSub_refl σ), F.res_refl_apply,
      ← F.opair_od_eq_opair_obd K σ (m + 1) c (K.ohom (m + 1) σ) (fun u hu => K.oSub_of_mem_support_ohom (m + 1) σ u hu),
      hc, opair_zero_cochain, sub_zero]
    rfl

end P2MW.S_AlgebraicGeometry_OModulePresheaf_sub_oext_ores_mem_of_od_eq_zero
