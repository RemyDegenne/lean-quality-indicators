@[expose] public section

universe v v' u u' w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

open scoped Simplicial

namespace SSet

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {X Y : SSet.{w}} (f : X ⟶ Y) (R : C)

section CoefficientComparison

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasCoproducts.{w} D]
  (L : C ⥤ D) [L.Additive]
  [∀ (T : Type w), PreservesColimitsOfShape (Discrete T) L]

section UnderlyingCoefficientMorphisms

theorem normalizedChainComplexFunctorObjCompMapIso_nondegComplexMap
    (S T : SSet.{w}) (Φ : S ⋙ sigmaConst.obj R ⟶ T ⋙ sigmaConst.obj R) :
    let ΦD : S ⋙ sigmaConst.obj (L.obj R) ⟶ T ⋙ sigmaConst.obj (L.obj R) :=
      Functor.whiskerLeft S (sigmaConstObjCompIso L R).inv ≫
        Functor.whiskerRight Φ L ≫
          Functor.whiskerLeft T (sigmaConstObjCompIso L R).hom
    (L.mapHomologicalComplex (.down ℕ)).map
        ((S.splitting.map (sigmaConst.obj R)).nondegComplexMap
          (T.splitting.map (sigmaConst.obj R)) Φ) ≫
        (normalizedChainComplexFunctorObjCompMapIso R L).hom.app T =
      (normalizedChainComplexFunctorObjCompMapIso R L).hom.app S ≫
        (S.splitting.map (sigmaConst.obj (L.obj R))).nondegComplexMap
          (T.splitting.map (sigmaConst.obj (L.obj R))) ΦD := by
  dsimp only
  apply normalizedChainComplex_comparison_of_chainComplex R L
  ext n : 1
  simp

end UnderlyingCoefficientMorphisms
end CoefficientComparison
end SSet
end
