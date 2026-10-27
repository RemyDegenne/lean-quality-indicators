set_option warningAsError true

set_option backward.isDefEq.respectTransparency false

@[expose] public section

namespace AlgebraicGeometry.RingedSpace.ClosedPointHom

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R] (X : RingedSpace.{u})

/-- A full ringed-space morphism induced by a map on global sections, with constant closed base. -/
noncomputable def hom (alpha : R →+* X.presheaf.obj (op ⊤)) :
    X ⟶ Spec.sheafedSpaceObj (CommRingCat.of R) where
  hom.base := base R X
  hom.c := {
    app := fun U => by
      by_cases hU : U = op (⊤ : Opens (Spec.sheafedSpaceObj (CommRingCat.of R) : TopCat))
      · subst U
        exact (StructureSheaf.globalSectionsIso (CommRingCat.of R)).inv ≫
          CommRingCat.ofHom alpha
      · have hu : unop U ≠ (⊤ : Opens (Spec.sheafedSpaceObj (CommRingCat.of R) : TopCat)) := by
          intro heq
          exact hU (by cases U; cases heq; rfl)
        exact (X.sheaf.isTerminalOfEqEmpty (preimage_eq_bot R X (unop U) hu)).from _
    naturality := by
      intro U V i
      by_cases hV : V = op (⊤ : Opens (Spec.sheafedSpaceObj (CommRingCat.of R) : TopCat))
      · have hU : U = op (⊤ : Opens (Spec.sheafedSpaceObj (CommRingCat.of R) : TopCat)) := by
          apply Opposite.unop_injective
          have hle : (⊤ : Opens (Spec.sheafedSpaceObj (CommRingCat.of R) : TopCat)) ≤ unop U := by
            have hv : unop V = ⊤ := congrArg unop hV
            simpa only [hv] using (unop i).le
          exact eq_top_iff.mpr hle
        subst U
        subst V
        have : i = 𝟙 _ := Subsingleton.elim _ _
        subst i
        erw [(Spec.sheafedSpaceObj (CommRingCat.of R)).presheaf.map_id]
        erw [((TopCat.Presheaf.pushforward CommRingCat (base R X)).obj X.presheaf).map_id]
        exact (Category.comp_id _).symm
      · have hv : unop V ≠ (⊤ : Opens (Spec.sheafedSpaceObj (CommRingCat.of R) : TopCat)) := by
          intro heq
          exact hV (by cases V; cases heq; rfl)
        apply (X.sheaf.isTerminalOfEqEmpty (preimage_eq_bot R X (unop V) hv)).hom_ext
  }

end AlgebraicGeometry.RingedSpace.ClosedPointHom
end
