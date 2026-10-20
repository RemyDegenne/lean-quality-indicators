@[expose] public section

open CategoryTheory Limits Opposite Functor

open scoped Simplicial

universe w v u vD uD

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

@[simp]
theorem equifiberedSigmaTransfer_app
    {D : Type uD} [Category.{vD} D] {F G : D ⥤ Type w} (p : F ⟶ G)
    (hp : NatTrans.Equifibered p)
    (hf : ∀ j (g : G.obj j), Finite {f : F.obj j // p.app j f = g}) (R : C) (j : D) :
    (equifiberedSigmaTransfer p hp hf R).app j =
      sigmaConstTransfer (p.app j) (hf j) R := rfl

end CategoryTheory
end
