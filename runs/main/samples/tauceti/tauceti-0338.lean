public section

noncomputable section

open CategoryTheory Limits Simplicial unitInterval

universe w v u

namespace TauCeti

section Cube

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

lemma cubeRelClass_singularHomologyMap {P : TopPair.{w}} (f : cubeBoundaryPair.{w} 1 ⟶ P) :
    cubeRelClass R ≫ TopPair.singularHomologyMap f R 1 =
      SSetPair.relClass₁ R (TopPair.toSSetPair.obj P)
        ((TopPair.toSSetPair.map f).right.app _ cubeSimplex)
        ((TopPair.toSSetPair.map f).left.app _ (cubeEndVertex 0 (Or.inl rfl)))
        ((TopPair.toSSetPair.map f).left.app _ (cubeEndVertex 1 (Or.inr rfl)))
        (SSetPair.δ_map_eq _ _ 1 _ δ_one_cubeSimplex)
        (SSetPair.δ_map_eq _ _ 0 _ δ_zero_cubeSimplex) := by
  rw [cubeRelClass]
  exact SSetPair.relClass₁_homologyMap R _ _ _ _ _ _

end Cube
end TauCeti
end
end
