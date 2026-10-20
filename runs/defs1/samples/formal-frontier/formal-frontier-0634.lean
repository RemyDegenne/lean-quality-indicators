@[expose] public section

open CategoryTheory Limits Opposite

open scoped Simplicial

universe w v u

namespace IsCoveringMap

variable {X Y : TopCat.{w}} {p : Y ⟶ X}

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

variable [CategoryWithHomology C]

/-- The ordinary singular homology transfer induced by the chain transfer. -/
noncomputable def singularHomologyTransfer (hp : IsCoveringMap p)
    (hf : ∀ x : X, Finite {y : Y // p y = x}) (R : C) (q : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor C q).obj R).obj X ⟶
      ((AlgebraicTopology.singularHomologyFunctor C q).obj R).obj Y :=
  SSet.homologyTransfer (TopCat.toSSet.map p) hp.toSSet_map_equifibered
    (fun s => by
      let := hf (X.toSSetObjEquiv (op ⦋0⦌) s default)
      exact hp.finite_singularLift (op ⦋0⦌) s default) R q

end IsCoveringMap
end
