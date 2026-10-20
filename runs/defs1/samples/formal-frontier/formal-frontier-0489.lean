@[expose] public section

open CategoryTheory Limits Opposite Functor

open scoped Simplicial

universe w v u vD uD

namespace SSet

variable {F G : SSet.{w}} (p : F ⟶ G) (hp : NatTrans.Equifibered p)

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- Transfer on the all-simplex chain complexes of an equifibered map, requiring
only finite vertex fibers and no constant degree. -/
noncomputable def chainComplexTransfer
    (hf : ∀ g : G _⦋0⦌, Finite {f : F _⦋0⦌ // p.app _ f = g}) (R : C) :
    G.chainComplex R ⟶ F.chainComplex R :=
  (AlgebraicTopology.alternatingFaceMapComplex C).map
    (equifiberedSigmaTransfer p hp (finite_fiber_of_finite_vertices p hp hf) R)

end SSet
end
