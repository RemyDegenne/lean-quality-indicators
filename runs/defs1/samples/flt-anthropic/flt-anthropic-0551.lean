namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_principalSeries2_of_jacquet_ne_top

set_option autoImplicit false

noncomputable section

namespace JacquetPS2

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal Matrix TopologicalSpace

section Group

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

scoped instance secondCountable_matrix : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → F))

scoped instance secondCountable_matrix_op : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isEmbedding.isInducing.secondCountableTopology

scoped instance secondCountable_gl : SecondCountableTopology G :=
  Units.isInducing_embedProduct.secondCountableTopology

local notation "ρ" => rightTranslate2 p

def diff (w : G → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ {D : G → ℂ | ∃ W' ∈ cyc p w, ∃ t : F,
    D = fun g : G => W' (g * UnramifiedWhittaker.unipotent t) - W' g}

end Group
end JacquetPS2
end
end P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_principalSeries2_of_jacquet_ne_top
