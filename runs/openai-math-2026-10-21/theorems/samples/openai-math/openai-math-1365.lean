namespace OAI

universe uA uC uD uK uV

noncomputable section

open MeasureTheory Set

open scoped BigOperators Classical

namespace ClassicalON

variable {V : Type uV} {K : Type uK} [Fintype V] [Fintype K]

variable (A : V → Type uA) (label : V → K)

variable [∀ v,MeasurableSpace (A v)]

theorem grouped_measurePreserving (μ : (v : V) → Measure (A v)) [∀ v,SigmaFinite (μ v)] :
    MeasurePreserving (groupedMeasurableEquiv A label)
      (Measure.pi (fun k : K => Measure.pi (fun v : {v // label v=k} => μ v.val))) (Measure.pi μ) := by
  refine ⟨(groupedMeasurableEquiv A label).measurable,?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [MeasurableEquiv.map_apply]
  have he : (groupedMeasurableEquiv A label) ⁻¹' (Set.pi Set.univ s)=
      Set.pi Set.univ (fun k : K => Set.pi Set.univ (fun v : {v // label v=k} => s v.val)) := by
    ext x
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_univ,true_implies]
    constructor
    · intro h k v
      have hv := h v.val
      rcases v with ⟨v,hv'⟩
      subst k
      exact hv
    · intro h v
      exact h (label v) ⟨v,rfl⟩
  rw [he,Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [← Fintype.prod_sigma (fun v : Σ k : K, {v // label v=k} => μ v.2.val (s v.2.val))]
  exact (Equiv.sigmaFiberEquiv label).prod_comp (fun v => μ v (s v))

end ClassicalON
end
end OAI
