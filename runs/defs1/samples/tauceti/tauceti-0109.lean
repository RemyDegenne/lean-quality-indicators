public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits

universe w v u

namespace TauCeti.MappingTorus

variable {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] (R : C)

/-- The singular-chain map induced by monodromy followed by fibre inclusion is chain-homotopic
to the fibre-inclusion chain map. -/
def singularChainHomotopy :
    _root_.Homotopy
      (monodromyChainMap φ R ≫ fibreInclusionChainMap φ R)
      (fibreInclusionChainMap φ R) := by
  let f : TopCat.of F ⟶ TopCat.of F := TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F))
  let i : TopCat.of F ⟶ TopCat.of (TauCeti.MappingTorus φ) :=
    TopCat.ofHom (TauCeti.MappingTorus.incl φ)
  refine (_root_.Homotopy.ofEq
    (((singularChainComplexFunctor C).obj R).map_comp f i).symm).trans ?_
  -- `TopCat.Homotopy (f ≫ i) i` unfolds to a homotopy between the underlying continuous maps,
  -- whose composite `(incl φ).comp φ` is exactly the source of `monodromyHomotopy φ`.
  exact (show TopCat.Homotopy (f ≫ i) i from
    TauCeti.MappingTorus.monodromyHomotopy φ).singularChainComplexFunctorObjMap R

end TauCeti.MappingTorus
end
end
