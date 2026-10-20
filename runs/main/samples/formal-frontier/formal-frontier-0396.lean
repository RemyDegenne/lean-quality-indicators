public section

open CategoryTheory TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

universe u

namespace Scheme.Hom

lemma appTop_restriction_square_of_eq
    {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (hV : V = f ⁻¹ᵁ U) :
    let _ : Algebra Γ(X, ⊤) Γ(X, U) :=
      (X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    let _ : Algebra Γ(Y, ⊤) Γ(Y, V) :=
      (Y.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    (algebraMap Γ(Y, ⊤) Γ(Y, V)).comp f.appTop.hom =
      (f.appLE U V hV.le).hom.comp (algebraMap Γ(X, ⊤) Γ(X, U)) := by
  subst V
  simpa only [Scheme.Hom.appLE_eq_app] using f.appTop_restriction_square U

end Scheme.Hom
end AlgebraicGeometry
end
end
