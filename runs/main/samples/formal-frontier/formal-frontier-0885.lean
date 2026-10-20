set_option warningAsError true

@[expose] public section

namespace Steinberg

universe uι uR uG

open scoped commutatorElement

variable {ι : Type uι} {R : Type uR} [Ring R]

section Elementary

variable [Fintype ι] [DecidableEq ι]

theorem toGL_range : (toGL (ι := ι) (R := R)).range =
    Matrix.GeneralLinearGroup.elementarySubgroup ι R := by
  apply le_antisymm
  · rintro g ⟨x, rfl⟩
    exact (toElementary x).property
  · intro g hg
    obtain ⟨x, hx⟩ := toElementary_surjective (⟨g, hg⟩ :
      Matrix.GeneralLinearGroup.elementarySubgroup ι R)
    exact ⟨x, congrArg Subtype.val hx⟩

end Elementary
end Steinberg
end
