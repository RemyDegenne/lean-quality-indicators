@[expose] public section

namespace TauCeti

namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {a : H →L[ℂ] H}

section Equiv

@[simp]
theorem coe_realSpectrumBddSymbolsEquiv (ha : IsSelfAdjoint a)
    (f : realSpectrumBddSymbols a) :
    ((realSpectrumBddSymbolsEquiv ha f : bddSymbols a) : spectrum ℂ a → ℂ)
      = (f : spectrum ℝ a → ℂ) ∘ realSpectrumHomeomorph ha :=
  coe_realSpectrumBddSymbolsEquiv_apply_aux ha f

end Equiv
end BorelCalculus
end TauCeti
end
