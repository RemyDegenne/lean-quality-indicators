public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSpor5

section Fi23Card

open CFSG.Sporadic.Fi23 CFSG.HardMathSupport.Timmesfeld.SporadicBalance

section Layer

theorem fi23FiveLayer_holds : Inputs2324.Fi23FiveLayer := by
  intro S _ _ hsp x hx
  obtain ⟨e₁⟩ := hsp
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv
  have e₂ : S ≃* CFSG.Blueprint.NativeSporadic.Fi23 := e₁.trans b.symm
  have e : S ≃* ↥J := e₂.trans fi23EquivJ
  obtain ⟨ψ, hψ, hψu⟩ := exists_injective_s12
  exact layer_of_facts_equiv (B := ↥J) (instB := inferInstance) e ψ hψ (fusion_J hψ hψu)
    card_centralizer_five_le Fi23Five.oPrimeCoreTrivialAt_Fi23J_five x hx

end Layer
end Fi23Card
end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSpor5
end
