public section

open CategoryTheory MonoidalCategory Opposite DirectSum

namespace TauCeti

open CategoryTheory.CommMon

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}} (A : CommMon (GradedObject ℕ X.Modules)) (U : X.Opens)

section Restriction

variable {U} {V : X.Opens} (f : V ⟶ U)

lemma _root_.CategoryTheory.CommMon.restrictGradedSections_comp {W : X.Opens} (g : W ⟶ V) :
    A.restrictGradedSections (g ≫ f) =
      (A.restrictGradedSections g).comp (A.restrictGradedSections f) :=
  DirectSum.ringHom_ext fun n x ↦ by simp

end Restriction
end
end TauCeti
end
