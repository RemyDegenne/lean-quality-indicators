@[expose] public section

open CategoryTheory Limits Opposite Functor

open scoped Simplicial

universe w v u vD uD

namespace SSet

variable {F G : SSet.{w}} (p : F ⟶ G) (hp : NatTrans.Equifibered p)

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

variable [CategoryWithHomology C]

theorem homologyTransfer_comp_map
    (hf : ∀ g : G _⦋0⦌, Finite {f : F _⦋0⦌ // p.app _ f = g})
    (R : C) (d q : ℕ)
    (hd : ∀ g : G _⦋0⦌, Nat.card {f : F _⦋0⦌ // p.app _ f = g} = d) :
    homologyTransfer p hp hf R q ≫ SSet.homologyMap p R q =
      d • 𝟙 (G.homology R q) := by
  let H := HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) q
  change H.map (chainComplexTransfer p hp hf R) ≫ H.map (chainComplexMap p R) =
    d • 𝟙 (H.obj (G.chainComplex R))
  rw [← H.map_comp, chainComplexTransfer_comp_map p hp hf R d hd,
    H.map_nsmul, H.map_id]

end SSet
end
