@[expose] public section

namespace FirstOrder.Language

open Cardinal

variable {s₀ : LocalStage} {M : Type} [(localColim s₀).Structure M] [LinearOrder M]
  [WellFoundedLT M] (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)

/-- **The schema term-model carrier**: closed `(localColim s₀)[[ℕ]]` terms quotiented by the
completed theory's equality. An `abbrev`, so `Quotient` lemmas and dot-notation apply
transparently (the `FSentence` precedent). -/
abbrev SchemaTermCarrier : Type := Quotient (schemaTermSetoid (s₀ := s₀) (M := M) hM)

end FirstOrder.Language
end
