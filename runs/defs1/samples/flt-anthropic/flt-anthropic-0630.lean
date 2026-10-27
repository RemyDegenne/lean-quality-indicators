namespace P2MW.S_AutomorphicForm_coversModCentre_and_archOccursInClassOf_iff_of_detWindow_le

set_option autoImplicit false

noncomputable section

namespace Ws23

namespace V2

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

variable {F : Type} [Field F] [NumberField F]

def omega {D : Set (AdelicGL2 (𝓞 F) F)} {Φ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F (pinsW D) Φ) : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ :=
  R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom

end V2
end Ws23
end
end P2MW.S_AutomorphicForm_coversModCentre_and_archOccursInClassOf_iff_of_detWindow_le
