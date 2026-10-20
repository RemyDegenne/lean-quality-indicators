public section

open CategoryTheory Limits

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
  [RelativeDimensionLE 1 f]

@[simp]
lemma mem_relativeEffectiveCartierDegreeSubfunctor_obj_iff
    {d : ℕ} {T : (Over S)ᵒᵖ} {D : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T} :
    D ∈ (relativeEffectiveCartierDegreeSubfunctor f d).obj T ↔
      (D.1.subschemeι ≫ pullback.fst T.unop.hom f).finrank = fun _ ↦ d :=
  Iff.rfl

end
end TauCeti.AlgebraicGeometry
end
