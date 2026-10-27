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

/-- Restriction of sections along an inclusion of opens `V ≤ U`, as a ring homomorphism between
the graded rings of sections. It sends each homogeneous section to its restriction, in the same
degree (`restrictGradedSections_of`). -/
def _root_.CategoryTheory.CommMon.restrictGradedSections :
    (⨁ n, Γ(A.X n, U)) →+* ⨁ n, Γ(A.X n, V) :=
  DirectSum.toSemiring
    (fun n ↦ (DirectSum.of (fun n ↦ Γ(A.X n, V)) n).comp ((A.X n).presheaf.map f.op).hom)
    ((congrArg _ (map_gOne_sections A f)).trans (DirectSum.of_zero_one _))
    (fun x y ↦ (congrArg _ (map_gMul_sections A f x y)).trans (DirectSum.of_mul_of _ _).symm)

end Restriction
end
end TauCeti
end
