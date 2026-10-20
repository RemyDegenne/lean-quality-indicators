public section

namespace TauCeti

variable {α : Type*} [MeasurableSpace α]

theorem measurable_list_getD (i : ℕ) (a : α) :
    Measurable (fun l : List α => l.getD i a) := by
  have h : Measurable (fun v : Σ n, Fin n → α => (List.ofFn v.2).getD i a) := by
    intro s hs
    apply MeasurableSpace.measurableSet_iInf.2
    intro n
    -- On the length-n stratum, the sigma preimage is evaluation on finite tuples.
    change MeasurableSet {f : Fin n → α | (List.ofFn f).getD i a ∈ s}
    have hf : Measurable (fun f : Fin n → α => (List.ofFn f).getD i a) := by
      by_cases hi : i < n
      · simpa [List.getD_eq_getElem, hi] using measurable_pi_apply (⟨i, hi⟩ : Fin n)
      · have heq (f : Fin n → α) : (List.ofFn f).getD i a = a :=
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)
        simp_rw [heq]
        exact measurable_const
    exact hf hs
  have hcomp : (fun v : Σ n, Fin n → α => (List.ofFn v.2).getD i a) ∘
      List.equivSigmaTuple = (fun l : List α => l.getD i a) := by
    funext l
    exact congrArg (fun l => l.getD i a) (List.ofFn_get l)
  rw [← hcomp]
  exact h.comp (comap_measurable List.equivSigmaTuple)

end TauCeti
end
