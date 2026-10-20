namespace P2MW.S_AutomorphicForm_exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology FLT.SmoothVectors

open scoped NNReal

noncomputable section

namespace WITNESS

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

variable (S₂ : Finset (HeightOneSpectrum (𝓞 F)))

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

def awayPart : AdelicGL2 (𝓞 F) F →* AdelicGL2 (𝓞 F) F := Units.map (awayMatHom F S)

end WITNESS
end
end P2MW.S_AutomorphicForm_exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth
