public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

variable {X Y : C} {f : X ⟶ Y}

theorem IsRightAlmostSplit.not_isSplitMono (hf : IsRightAlmostSplit f) [Epi f] :
    ¬ IsSplitMono f := fun _ ↦ hf.not_isIso (isIso_of_epi_of_isSplitMono f)

end TauCeti
end
