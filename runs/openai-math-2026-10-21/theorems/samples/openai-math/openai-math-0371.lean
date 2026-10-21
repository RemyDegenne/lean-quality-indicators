namespace OAI

universe u

namespace PiExponentSeshadri.Frames

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

open scoped AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

lemma restrictSection_congr {φ ψ : Y ⟶ X} (h : φ = ψ)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] {M : X.Modules} (s : O X ⟶ M) :
    restrictSection φ s ≫ (Scheme.Modules.restrictFunctorCongr h).hom.app M =
      restrictSection ψ s := by
  subst ψ
  have H : (Scheme.Modules.restrictFunctorCongr (show φ = φ from rfl)).hom.app M = 𝟙 _ := by
    ext U a
    simp
    rfl
  rw [H, Category.comp_id]

end
end PiExponentSeshadri.Frames
end OAI
