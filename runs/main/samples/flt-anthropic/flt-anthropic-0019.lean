namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse

open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion

open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory UnramifiedWhittaker AdelicDock

open LanglandsTunnell.TateLocal NumberField.StandardAddChar Topology

open scoped nonZeroDivisors NNReal ENNReal Matrix Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace KcRsCellChoice

section MultiPlace

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

open scoped Classical in
theorem embS_mulSingle (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) :
    embS SQ (Pi.mulSingle p x) = embAt (p : HeightOneSpectrum (𝓞 ℚ)) x :=
  MonoidHom.noncommPiCoprod_mulSingle
    (N := fun q : ↥SQ => GL (Fin 2) ((q : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))
    (fun q : ↥SQ => embAt (q : HeightOneSpectrum (𝓞 ℚ))) p x

end MultiPlace
end KcRsCellChoice
end
end P2MW.S_LanglandsTunnell_RankinSelberg_exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots
