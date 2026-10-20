@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Opposite

universe v u w

namespace CategoryTheory.NatTrans

variable {C : Type u} [Category.{v} C]

variable {H G : Functor C GrpCat.{w}} (i : H ⟶ G)

variable {K : Functor C (Type w)}

/-- A natural transformation out of `G` which is constant on the left cosets
of `i(H)` descends to the pointwise coset functor. -/
def cosetLift (f : G ⋙ CategoryTheory.forget GrpCat.{w} ⟶ K)
    (hf : ∀ X x y, QuotientGroup.leftRel (i.app X).hom.range x y →
      f.app X x = f.app X y) :
    coset i ⟶ K where
  app X := ↾(fun x ↦ x.liftOn' (f.app X) (hf X))
  naturality X Y g := by
    ext x
    induction x using Quotient.inductionOn'
    exact NatTrans.naturality_apply f g _

end CategoryTheory.NatTrans
end
end
