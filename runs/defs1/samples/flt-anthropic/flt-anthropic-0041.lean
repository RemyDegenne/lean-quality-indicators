namespace P2MW.S_MvFormalGroup_BigWittLaw_subst_artinHasse_frobFam

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

noncomputable section

universe u

open PowerSeries MvFormalGroup MvFormalGroup.ArtinHasse

namespace LambdaGhost

open PowerSeries

section Ghost

variable {A : Type*} [CommRing A]

abbrev inv1 (f : A⟦X⟧) : A⟦X⟧ := f.invOfUnit 1

end Ghost
end LambdaGhost
end
end P2MW.S_MvFormalGroup_BigWittLaw_subst_artinHasse_frobFam
