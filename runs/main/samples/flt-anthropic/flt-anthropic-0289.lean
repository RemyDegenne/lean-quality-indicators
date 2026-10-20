namespace P2MW.S_AutomorphicForm_exists_isKfSmooth_eq_prod_localChar_of_borel_fin_of_level

attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

noncomputable section

namespace RS11SC

open MeasureTheory NumberField NumberField.AdelicHeight NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain Matrix AdelicDock FLT.SmoothVectors

open scoped NNReal Classical

variable {K : Type} [Field K] [NumberField K]

theorem valued_sel (g : AdelicGL2 (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (sel g v) = max (Valued.v (ent g 1 0 v)) (Valued.v (ent g 1 1 v)) := by
  unfold sel
  split_ifs with h
  · rw [max_eq_right h]
  · rw [max_eq_left (le_of_lt (not_le.mp h))]

end RS11SC
end
end P2MW.S_AutomorphicForm_exists_isKfSmooth_eq_prod_localChar_of_borel_fin_of_level
