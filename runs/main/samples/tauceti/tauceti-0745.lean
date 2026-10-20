public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {k R : Type u} [Field k] [CommRing R] [IsLocalRing R] [IsArtinianRing R]
  [Algebra k R] (E : EllipticCurveGeom (Spec (.of R)))
  (p : ℕ) [Fact p.Prime] [CharP k p] [CharP R p]

theorem exists_iso_baseChange_iterateFrobenius
    (hres : Function.Bijective (algebraMap k (ResidueField R))) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ E₀ : EllipticCurveGeom (Spec (.of k)),
      ∃ e : (E.baseChange (Spec.map (CommRingCat.ofHom (iterateFrobenius R p n)))).carrier ≅
          (E₀.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k R)))).carrier,
        e.hom ≫ (E₀.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k R)))).structureMap =
            (E.baseChange (Spec.map (CommRingCat.ofHom (iterateFrobenius R p n)))).structureMap ∧
          (E.baseChange (Spec.map (CommRingCat.ofHom (iterateFrobenius R p n)))).zero ≫ e.hom =
            (E₀.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k R)))).zero := by
  obtain ⟨N, hN⟩ := TauCeti.exists_iterateFrobenius_eq_algebraMap_comp (R := R) p hres
  refine ⟨N, fun n hn ↦ ?_⟩
  let f := (iterateFrobenius k p n).comp
    ((RingEquiv.ofBijective (algebraMap k (ResidueField R)) hres).symm.toRingHom.comp (residue R))
  let a : Spec (.of k) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom f)
  let b : Spec (.of R) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k R))
  let F : Spec (.of R) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (iterateFrobenius R p n))
  have hF : b ≫ a = F := by
    rw [← Spec.map_comp]
    exact congrArg (fun g : R →+* R ↦ Spec.map (CommRingCat.ofHom g)) (hN n hn).symm
  let E₀ := E.baseChange a
  let E' := E₀.baseChange b
  let E'' := E.baseChange F
  let g₀ := (E.baseChangeIso a).hom ≫ pullback.fst E.structureMap a
  let g' := (E₀.baseChangeIso b).hom ≫ pullback.fst E₀.structureMap b
  let g'' := (E.baseChangeIso F).hom ≫ pullback.fst E.structureMap F
  have h' : IsPullback (g' ≫ g₀) E'.structureMap E.structureMap F := by
    simpa only [hF] using
      (E₀.isPullback_baseChange b).paste_horiz (E.isPullback_baseChange a)
  have h'' : IsPullback g'' E''.structureMap E.structureMap F := E.isPullback_baseChange F
  let e := h''.isoIsPullback _ _ h'
  refine ⟨E₀, e, h''.isoIsPullback_hom_snd _ _ h', ?_⟩
  apply h'.hom_ext
  · rw [Category.assoc, h''.isoIsPullback_hom_fst _ _ h']
    simp only [g'', g', g₀, E₀, F, b, Category.assoc, zero_baseChangeIso_hom_assoc,
      pullbackSection_fst, pullbackSection_fst_assoc, ← hF]
  · rw [Category.assoc, h''.isoIsPullback_hom_snd _ _ h']
    exact E''.zero_comp.trans E'.zero_comp.symm

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
end
