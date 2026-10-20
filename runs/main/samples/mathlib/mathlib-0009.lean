@[expose] public section

noncomputable section

universe w v v' u u'

open CategoryTheory

open CategoryTheory.Category

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

variable (D : Type u') [Category.{v'} D]

attribute [instance_reducible, instance] HasZeroMorphisms.zero

variable {C D}

open Opposite HasZeroMorphisms

open ZeroObject

section

variable [HasZeroMorphisms C] [HasZeroObject C] {F : D ⥤ C}

omit [HasZeroObject C] in
lemma _root_.CategoryTheory.Functor.FullyFaithful.hasZeroMorphisms_def (hF : F.FullyFaithful)
    (X Y : D) : letI : HasZeroMorphisms D := hF.hasZeroMorphisms
    (0 : X ⟶ Y) = hF.preimage 0 := rfl

end
end CategoryTheory.Limits
end
end
