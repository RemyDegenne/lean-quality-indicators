set_option warningAsError true

set_option backward.isDefEq.respectTransparency false

@[expose] public section

namespace AlgebraicGeometry.RingedSpace.ClosedPointHom

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R] (X : RingedSpace.{u})

/-- Maps on global sections classify full ringed morphisms with the fixed closed base. -/
noncomputable def equiv :
    (R →+* X.presheaf.obj (op ⊤)) ≃
      { f : X ⟶ Spec.sheafedSpaceObj (CommRingCat.of R) // f.hom.base = base R X } where
  toFun alpha := ⟨hom R X alpha, rfl⟩
  invFun f := (globalSectionsMap R X f.1).hom
  left_inv alpha := by
    change (globalSectionsMap R X (hom R X alpha)).hom = alpha
    rw [hom_globalSectionsMap]
    rfl
  right_inv f := by
    apply Subtype.ext
    apply ext R X (hom_base R X _) f.2
    simp only [hom_globalSectionsMap, CommRingCat.ofHom_hom]

end AlgebraicGeometry.RingedSpace.ClosedPointHom
end
