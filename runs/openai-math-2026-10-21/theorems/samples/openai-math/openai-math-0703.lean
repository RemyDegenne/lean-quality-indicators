namespace OAI

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SeparableSpace H] [MeasurableSpace H] [BorelSpace H]

theorem measurable_conjugation_on_strongUnitarySpace
    (ξ : ℕ → H) (hξ : DenseRange ξ) (T : X → H →L[ℂ] H)
    (hT : ∀ x, Measurable (fun p => T p x)) (x : H) :
    Measurable (fun p : X × StrongUnitarySpace ξ =>
      unitaryConj (decodeStrongUnitary ξ p.2) (T p.1) x) := by
  have : PolishSpace (StrongUnitarySpace ξ) := strongUnitarySpace_polish ξ hξ
  have hU (y : H) : Measurable (fun p : X × StrongUnitarySpace ξ =>
      (decodeStrongUnitary ξ p.2 : H →L[ℂ] H) y) :=
    (continuous_decodeStrongUnitary_apply ξ hξ y).measurable.comp measurable_snd
  have hUs : Measurable (fun p : X × StrongUnitarySpace ξ =>
      (star (decodeStrongUnitary ξ p.2) : H →L[ℂ] H) x) :=
    (continuous_star_decodeStrongUnitary_apply ξ hξ x).measurable.comp measurable_snd
  have hTx := measurable_operator_field_apply (fun p : X × StrongUnitarySpace ξ => T p.1)
    (fun y => (hT y).comp measurable_fst) _ hUs
  exact measurable_operator_field_apply
    (fun p : X × StrongUnitarySpace ξ => (decodeStrongUnitary ξ p.2 : H →L[ℂ] H)) hU _ hTx

end
end KadisonKastler
end OAI
