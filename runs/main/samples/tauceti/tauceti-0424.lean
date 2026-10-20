public section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α : Type*}

variable [MeasurableSpace α]

theorem preimage_pairReindex_eq_self_of_measurableSet_arrayTail
    {s : Set (ℕ × ℕ → α)}
    (hs : MeasurableSet[arrayTail (fun p (x : ℕ × ℕ → α) => x p)] s)
    {σ τ : Equiv.Perm ℕ} (hσ : (MulAction.fixedBy ℕ σ)ᶜ.Finite)
    (hτ : (MulAction.fixedBy ℕ τ)ᶜ.Finite) : pairReindex (α := α) σ τ ⁻¹' s = s := by
  obtain ⟨M, hM⟩ := finite_compl_fixedBy_eventually_eq_self hσ
  obtain ⟨N, hN⟩ := finite_compl_fixedBy_eventually_eq_self hτ
  exact preimage_pairReindex_eq_of_measurable_arrayTailFamily
    ((measurableSet_arrayTail_iff.mp hs) (max M N))
    (fun k hk => hM k ((le_max_left M N).trans hk)) fun k hk => hN k ((le_max_right M N).trans hk)

end Probability
end TauCeti
end
