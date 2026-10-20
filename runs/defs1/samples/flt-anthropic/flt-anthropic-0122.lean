namespace P2MW.S_LocalGL2_exists_borelEigenfunctional_ne_zero_of_span_unipotentGL2_sub_ne_top

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.style.longLine false

noncomputable section

open IsDedekindDomain NumberField

open FLT.SmoothAdmissibleSchurCommutant

open scoped WithZero

namespace JacquetEmbeddingGL2

section Rep

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

variable {V : Type} [AddCommGroup V] [Module ℂ V]

local notation "F" => HeightOneSpectrum.adicCompletion K v

local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)

local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)

variable (π : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) →* Module.End ℂ V)

def VN : Submodule ℂ V :=
  Submodule.span ℂ {y : V | ∃ (t : HeightOneSpectrum.adicCompletion K v) (z : V),
    y = π (AutomorphicForm.unipotentGL2 t) z - z}

end Rep
end JacquetEmbeddingGL2
end
end P2MW.S_LocalGL2_exists_borelEigenfunctional_ne_zero_of_span_unipotentGL2_sub_ne_top
