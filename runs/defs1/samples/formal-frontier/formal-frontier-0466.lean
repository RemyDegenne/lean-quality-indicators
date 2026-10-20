@[expose] public section

open CategoryTheory CategoryTheory.IsCofiltered Set

universe u v w

namespace CategoryTheory.Functor

variable {I : Type u} {J : Type v} [Preorder I] [Preorder J]

/-- Evaluation of a compatible section lands in the eventual range. -/
def evalSectionToEventualRange (F : Jᵒᵖ ⥤ Type w) (i : Jᵒᵖ) :
    F.sections → F.eventualRange i :=
  fun x ↦ ⟨x.val i, F.mem_eventualRange_iff.2 fun _ g ↦ ⟨x.val _, x.property g⟩⟩

end CategoryTheory.Functor
end
