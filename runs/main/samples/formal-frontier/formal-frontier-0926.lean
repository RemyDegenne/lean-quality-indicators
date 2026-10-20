@[expose] public section

open CategoryTheory Limits Opposite

open scoped Simplicial

universe w v u

namespace IsCoveringMap

variable {X Y : TopCat.{w}} {p : Y ⟶ X}

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

variable [CategoryWithHomology C]

theorem singularHomologyTransfer_eq_map (hp : IsCoveringMap p)
    (hf : ∀ x : X, Finite {y : Y // p y = x}) (R : C) (q : ℕ) :
    hp.singularHomologyTransfer hf R q =
      (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) q).map
        (hp.singularChainComplexTransfer hf R) :=
  rfl

end IsCoveringMap
end
