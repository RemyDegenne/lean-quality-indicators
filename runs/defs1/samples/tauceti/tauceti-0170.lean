public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits

universe w v u

namespace TauCeti.MappingTorus

variable {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] (R : C)

/-- The fibre inclusion after `id - φ_*` is null-homotopic.  The sign is chosen so that the
endomorphism on the fibre is literally `id - φ_*`, rather than its negative. -/
noncomputable def wangNullHomotopy :
    _root_.Homotopy
      (wangEndomorphism φ R ≫ fibreInclusionChainMap φ R) 0 :=
  (_root_.Homotopy.ofEq
      (by rw [wangEndomorphism_def, Preadditive.sub_comp, Category.id_comp])).trans
    (_root_.Homotopy.equivSubZero (singularChainHomotopy φ R).symm)

end TauCeti.MappingTorus
end
end
