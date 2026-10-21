namespace OAI

namespace Ostmann

open scoped Classical

theorem WordTransferTemplate.branching_denominator_period {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (B : ℕ) (hB : 1 ≤ B)
    (hwords : template.WordsBounded B) (s : ℤ)
    (hs : s ∣ (historyFrequencyBase (internalFrequencyList n t) : ℤ)) :
    (∀ z ∈ (template.branching t hn).formulaLeaves .prime,
      z.2.cleared.denominator * s ∣
        (historyFrequencyPeriod (internalFrequencyList n t) (B ^ (n + 1) + 1) : ℤ)) ∧
    (∀ F ∈ (template.branching t hn).pivotFormulas .prime,
      F.cleared.denominator * s ∣
        (historyFrequencyPeriod (internalFrequencyList n t) (B ^ (n + 1) + 1) : ℤ)) := by
  have hfreq := template.branching_frequencies_dvd t hn
    (historyFrequencyBase (internalFrequencyList n t) : ℤ)
    (fun s hs => frequency_dvd_historyFrequencyBase _ s hs) .prime
    (by intro i s hs; simp only [HistoryFormula.frequencies, List.not_mem_nil] at hs)
  have hcost := template.branching_formula_cost t hn B 1 hB (by omega) hwords .prime (fun _ => le_rfl)
  have hperiod (F : HistoryFormula σ) (hf : ∀ d ∈ F.frequencies,
      d ∣ (historyFrequencyBase (internalFrequencyList n t) : ℤ))
      (hc : F.cost ≤ B ^ (n + 1)) :
      F.cleared.denominator * s ∣
        (historyFrequencyPeriod (internalFrequencyList n t) (B ^ (n + 1) + 1) : ℤ) := by
    simp only [historyFrequencyPeriod, Nat.cast_pow]
    exact (F.denominator_test_period _ s hf hs).trans
      (pow_dvd_pow _ (Nat.add_le_add_right (F.frequency_count_le_cost.trans hc) 1))
  constructor
  · intro z hz
    exact hperiod z.2 (hfreq.1 z hz) (by simpa only [Nat.one_mul] using hcost.1 z hz)
  · intro F hF
    exact hperiod F (hfreq.2 F hF) (by simpa only [Nat.one_mul] using hcost.2 F hF)

end Ostmann
end OAI
