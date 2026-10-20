public section

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (X : Scheme.{u}) [IsAffine X]

@[simp]
lemma relativeSpecAffineIso_inv_app_left (A : (QuasicoherentAlgebra X)ᵒᵖ) :
    ((relativeSpecAffineIso X).inv.app A).left =
      A.unop.obj.relativeSpecCover.f ⟨⊤, isAffineOpen_top X⟩ := by
  exact A.unop.obj.relativeSpecIsoSpec_inv

end
end TauCeti.AlgebraicGeometry
end
