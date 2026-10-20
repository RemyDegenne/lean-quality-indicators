namespace P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq

set_option autoImplicit false

set_option Elab.async false

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Fold_TateFubini

set_option autoImplicit false

p2m_open

open M4aLocalCFT LanglandsTunnell.TateLocal

open scoped NNReal ENNReal

noncomputable section

namespace NumberField

namespace TateGlobal

p2m_open

variable {F : Type} [Field F] [NumberField F]

section AlongAsm

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

theorem asm_val_snd_apply_of_mem (q : Q (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    (((asm S q : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v
      = ((q.2.1 ⟨v, hv⟩ : (v.adicCompletion F)ˣ) : v.adicCompletion F) :=
  congrArg (fun u : (v.adicCompletion F)ˣ => (u : v.adicCompletion F)) (unitAtHom_asm_of_mem S q hv)

end AlongAsm
end TateGlobal
end NumberField
end
end Fold_TateFubini
end P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq
