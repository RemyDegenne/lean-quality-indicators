namespace OAI

namespace SharpRamseyFive.FiniteEntropy

open scoped Classical BigOperators

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]

lemma first_entropy_of_partner_cap (p : Law (α×β)) (M : ℝ) (_hM : 0<M)
    (hpartner : ∀ a,0<first p a →
      (((support p).filter fun z=>z.1=a).card:ℝ)≤M) :
    entropy p ≤ entropy (first p)+Real.log M := by
  have hh := entropy_partition_bound p Prod.fst (fun _=>Real.log M) (by
    intro a ha
    rw [map_fst] at ha
    have hc:=hpartner a ha
    have hp : 0<(((support p).filter fun z=>z.1=a).card:ℝ) := by
      obtain ⟨z,hz,hf⟩ := map_positive p Prod.fst a (by simpa [map_fst] using ha)
      exact_mod_cast Finset.card_pos.mpr ⟨z,Finset.mem_filter.mpr ⟨(mem_support p z).mpr hz,hf⟩⟩
    exact Real.log_le_log hp hc)
  simpa only [map_fst,←Finset.sum_mul,(first p).sum_one,one_mul] using hh

end
end SharpRamseyFive.FiniteEntropy
end OAI
