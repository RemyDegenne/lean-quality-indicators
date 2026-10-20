@[expose] public section

noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

variable {P Q : C} (f : P ⟶ Q)

section Comparison

variable [HasCokernel f] [HasKernel f] [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)]

/-- An alternative formulation of the canonical map from the abelian coimage to the abelian image.
-/
def coimageImageComparison' : Abelian.coimage f ⟶ Abelian.image f :=
  kernel.lift (cokernel.π f) (cokernel.desc (kernel.ι f) f (by simp)) (by ext; simp)

end Comparison
end CategoryTheory.Abelian
end
end
