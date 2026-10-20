@[expose] public section

universe w v v' u u'

open CategoryTheory Opposite

noncomputable section

namespace CategoryTheory

namespace MorphismProperty

section

variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D] {E : Type*} [Category* E]

section

variable (P : MorphismProperty C)

/-- The family of morphisms indexed by `P.toSet` which corresponds
to `P : MorphismProperty C`, see `MorphismProperty.ofHoms_homFamily`. -/
def homFamily (f : P.toSet) : f.1.left ⟶ f.1.right := f.1.hom

end
end
end MorphismProperty
end CategoryTheory
end
end
