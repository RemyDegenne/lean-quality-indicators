@[expose] public noncomputable section

universe u

open TopCat AlgebraicGeometry TopologicalSpace CategoryTheory Opposite

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

namespace AlgebraicGeometry

open _root_.PrimeSpectrum

namespace Scheme.Modules

variable {M : (Spec R).Modules} {U V : (Spec R).Opens}

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma restrictAppIso_smul_Spec {S : CommRingCat.{u}} (f : R ⟶ S)
    [IsOpenImmersion (Spec.map f)] {U : (Spec S).Opens} (r : R)
    (x : Γ(M.restrict (Spec.map f), U)) :
    dsimp% (M.restrictAppIso (Spec.map f) U).hom (f r • x) =
      r • (M.restrictAppIso (Spec.map f) U).hom x := by
  rw [smul_Spec_def, smul_Spec_def]
  simp_rw [smul_restrictAppIso_hom_apply, ← ConcreteCategory.comp_apply, Category.assoc]
  have :
      f ≫ (ΓSpecIso S).inv ≫ (Spec S).presheaf.map U.leTop.op ≫ (Hom.appIso (Spec.map f) U).inv =
        (ΓSpecIso R).inv ≫ (Spec R).presheaf.map (Spec.map f ''ᵁ U).leTop.op := by
    simp [Iso.cancel_iso_inv_left, Hom.app_eq_appLE]
    rfl
  rw [this]

end Scheme.Modules
end AlgebraicGeometry
end
