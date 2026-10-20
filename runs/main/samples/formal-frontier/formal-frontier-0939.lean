@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
  UnitriangularStageCoordinateRing

open scoped CategoryTheory CategoryTheory.MonObj

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

variable (K : Type) [CommRing K] (n r : ℕ)

theorem unitriangularStageSuccessor_existsUnique_of_coordinates
    {X : Scheme}
    (f : X ⟶ Spec (.of (CoordinateRing K n r)))
    (hcoord : ∀ ij : Matrix.UnitriangularGroup.superdiagonalIndex n r,
      ij.1.1 < ij.1.2 →
      (((Scheme.ΓSpecIso (.of (CoordinateRing K n r))).inv ≫ f.appTop).hom)
        (coordinate K n r ij) = 0) :
    ∃! g : X ⟶ Spec (.of (CoordinateRing K n (r + 1))),
      g ≫ (unitriangularStageSuccessor K n r).hom.hom.left = f := by
  let ambientMap : X ⟶ Spec (.of (Ambient K n)) :=
    f ≫ Spec.map (CommRingCat.ofHom (quotient K n r).toRingHom)
  have hpreimage :
      (Scheme.ΓSpecIso (.of (Ambient K n))).inv ≫ ambientMap.appTop =
        CommRingCat.ofHom (quotient K n r).toRingHom ≫
          ((Scheme.ΓSpecIso (.of (CoordinateRing K n r))).inv ≫ f.appTop) :=
    preimage_spec_comp f (CommRingCat.ofHom (quotient K n r).toRingHom)
  have hI : ideal K n (r + 1) ≤
      RingHom.ker ((Scheme.ΓSpecIso (.of (Ambient K n))).inv ≫
        ambientMap.appTop).hom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, j, hij, hgap, rfl⟩
    apply RingHom.mem_ker.mpr
    have heval := congrArg (fun arrow : CommRingCat.of (Ambient K n) ⟶ Γ(X, ⊤) =>
      arrow.hom (entry K n i j)) hpreimage
    rw [heval]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    change (((Scheme.ΓSpecIso (.of (CoordinateRing K n r))).inv ≫ f.appTop).hom)
      ((quotient K n r) (entry K n i j)) = 0
    by_cases hsmall : j.val < i.val + r
    · rw [quotient_entry K n r i j hij hsmall, map_zero]
    · have heq : j.val = i.val + r := by omega
      exact hcoord ⟨(i, j), heq⟩ hij
  let lift : X ⟶ Spec (.of (CoordinateRing K n (r + 1))) :=
    Scheme.Hom.liftQuotient ambientMap (ideal K n (r + 1)) hI
  have hstage : (unitriangularStageSuccessor K n r).hom.hom.left ≫
      (unitriangularStageInclusion K n r).hom.hom.left =
      (unitriangularStageInclusion K n (r + 1)).hom.hom.left := by
    simpa only [Grp.comp_hom_hom, Over.comp_left] using
      congrArg (fun arrow : unitriangularStageScheme K n (r + 1) ⟶
        unitriangularGroupScheme K (Fin n) => arrow.hom.hom.left)
        (unitriangularStageSuccessor_inclusion K n r)
  have hclosedAmbient : IsClosedImmersion
      (unitriangularStageInclusion K n r).hom.hom.left :=
    unitriangularStageInclusion_isClosedImmersion K n r
  have : Mono (unitriangularStageInclusion K n r).hom.hom.left :=
    (IsClosedImmersion.iff_isFinite_and_mono _).mp hclosedAmbient |>.2
  have hlift : lift ≫ (unitriangularStageSuccessor K n r).hom.hom.left = f := by
    apply (cancel_mono (unitriangularStageInclusion K n r).hom.hom.left).mp
    calc
      (lift ≫ (unitriangularStageSuccessor K n r).hom.hom.left) ≫
          (unitriangularStageInclusion K n r).hom.hom.left =
          lift ≫ (unitriangularStageInclusion K n (r + 1)).hom.hom.left := by
            rw [Category.assoc, hstage]
      _ = ambientMap := Scheme.Hom.liftQuotient_comp ambientMap _ hI
      _ = f ≫ (unitriangularStageInclusion K n r).hom.hom.left := rfl
  refine ⟨lift, hlift, ?_⟩
  intro g hg
  have hclosed : IsClosedImmersion
      (unitriangularStageSuccessor K n r).hom.hom.left :=
    unitriangularStageSuccessor_isClosedImmersion K n r
  have : Mono (unitriangularStageSuccessor K n r).hom.hom.left :=
    (IsClosedImmersion.iff_isFinite_and_mono _).mp hclosed |>.2
  exact (cancel_mono (unitriangularStageSuccessor K n r).hom.hom.left).mp
    (hg.trans hlift.symm)

end AlgebraicGeometry
end
end
