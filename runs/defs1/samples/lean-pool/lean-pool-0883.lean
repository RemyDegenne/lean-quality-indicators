@[expose] public section

namespace FirstOrder.Language

open Filter

variable {s₀ : LocalStage} {M : Type} [(localColim s₀).Structure M]

/-- **The schema-template Ω-witness property.** For the schema template `tailTemplateOfSeq a`,
over the canonical de-substituted formulas of colimit-family connectives: a disjunction's
template truth yields one component's template truth, and joint component template truth yields
the conjunction's. This is the countable, `J`-free witnessing the ω-stage Henkin completion
will establish; here it is the input to the normal-form bridge. -/
structure TailTemplateOmegaWitnessed (s₀ : LocalStage) {M : Type}
    [(localColim s₀).Structure M] (a : ℕ → M) : Prop where
  /-- A family disjunction's `canonDeForm` template-true ⟹ some component's is. -/
  iSup_witnessed : ∀ {m : ℕ} (φs : ℕ → (localColim s₀).BoundedFormulaω Empty m),
    (⟨m, BoundedFormulaω.iSup φs⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈
      ΓlocalColim s₀ →
    ∀ {p : ℕ} (g : Fin m → (localColim s₀).Term (Fin p)),
    (tailTemplateOfSeq (L := localColim s₀) a).truth
        (canonDeForm (localColim s₀) (BoundedFormulaω.iSup φs) g) →
    ∃ i, (tailTemplateOfSeq (L := localColim s₀) a).truth
        (canonDeForm (localColim s₀) (φs i) g)
  /-- All components' `canonDeForm` template-true ⟹ the family conjunction's is. -/
  iInf_witnessed : ∀ {m : ℕ} (φs : ℕ → (localColim s₀).BoundedFormulaω Empty m),
    (⟨m, BoundedFormulaω.iInf φs⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈
      ΓlocalColim s₀ →
    ∀ {p : ℕ} (g : Fin m → (localColim s₀).Term (Fin p)),
    (∀ i, (tailTemplateOfSeq (L := localColim s₀) a).truth
        (canonDeForm (localColim s₀) (φs i) g)) →
    (tailTemplateOfSeq (L := localColim s₀) a).truth
        (canonDeForm (localColim s₀) (BoundedFormulaω.iInf φs) g)

end FirstOrder.Language
end
