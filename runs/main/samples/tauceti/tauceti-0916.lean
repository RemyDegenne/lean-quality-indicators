public section

open Filter Polynomial Topology

namespace TauCeti

namespace Sym

section AlgClosed

variable {𝕜 : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] {n : ℕ}

theorem exists_analyticAt_coeffEquiv_ofFn_localInverse {z : Fin n → 𝕜}
    (hz : Function.Injective z) :
    ∃ Ψ : (Fin n → 𝕜) → (Fin n → 𝕜), Ψ (coeffEquiv 𝕜 n (ofFn z)) = z ∧
      AnalyticAt 𝕜 Ψ (coeffEquiv 𝕜 n (ofFn z)) ∧
      (∀ᶠ w in 𝓝 z, Ψ (coeffEquiv 𝕜 n (ofFn w)) = w) ∧
      (∀ᶠ c in 𝓝 (coeffEquiv 𝕜 n (ofFn z)), coeffEquiv 𝕜 n (ofFn (Ψ c)) = c) := by
  obtain ⟨Ψ, hΨ₀, hΨa, hΨ⟩ :=
    exists_analyticAt_coeffEquiv_symm_eq_ofFn hz (Equiv.symm_apply_apply (coeffEquiv 𝕜 n) (ofFn z))
  have hσ : ContinuousAt (fun w : Fin n → 𝕜 => coeffEquiv 𝕜 n (ofFn w)) z :=
    (analyticAt_coeffEquiv_ofFn z).continuousAt
  refine ⟨Ψ, hΨ₀, hΨa, ?_, ?_⟩
  · -- Each `Ψ i` of a nearby coefficient tuple is one of the nearby roots, and proximity to the
    -- distinct `z i` forces it to be the `i`-th one.
    have hmem : ∀ᶠ w in 𝓝 z, ∀ i, ∃ j, w j = Ψ (coeffEquiv 𝕜 n (ofFn w)) i := by
      filter_upwards [hσ.eventually hΨ] with w hw i
      rw [Equiv.symm_apply_apply] at hw
      have hmem : Ψ (coeffEquiv 𝕜 n (ofFn w)) i ∈ ofFn (Ψ (coeffEquiv 𝕜 n (ofFn w))) :=
        mem_ofFn.2 ⟨i, rfl⟩
      rw [← hw] at hmem
      exact mem_ofFn.1 hmem
    have hne : ∀ i j : Fin n,
        ∀ᶠ w in 𝓝 z, i ≠ j → Ψ (coeffEquiv 𝕜 n (ofFn w)) i ≠ w j := by
      intro i j
      rcases eq_or_ne i j with rfl | hij
      · exact .of_forall fun _ h => absurd rfl h
      · have hΨi : ContinuousAt (fun w : Fin n → 𝕜 => Ψ (coeffEquiv 𝕜 n (ofFn w)) i) z :=
          ContinuousAt.comp' (f := fun w : Fin n → 𝕜 => coeffEquiv 𝕜 n (ofFn w))
            (analyticAt_pi_iff.1 hΨa i).continuousAt hσ
        filter_upwards [(hΨi.ne_iff_eventually_ne (continuousAt_apply j z)).1
          (by rw [hΨ₀]; exact fun h => hij (hz h))] with w hw _ using hw
    filter_upwards [hmem, eventually_all.2 fun i => eventually_all.2 fun j => hne i j] with
      w hw hwne
    refine funext fun i => ?_
    obtain ⟨j, hj⟩ := hw i
    rcases eq_or_ne i j with rfl | hij
    · exact hj.symm
    · exact absurd hj.symm (hwne i j hij)
  · filter_upwards [hΨ] with c hc
    rw [← hc, Equiv.apply_symm_apply]

end AlgClosed
end Sym
end TauCeti
end
