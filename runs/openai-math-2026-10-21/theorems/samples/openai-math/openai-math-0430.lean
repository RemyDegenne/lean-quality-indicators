namespace OAI

namespace SeparableQuotient

open Set Metric

open scoped BigOperators Topology

universe u

variable {𝕜 : Type} [RCLike 𝕜]

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

@[reducible] noncomputable local instance prefixDualNormedGroup :
    NormedAddCommGroup (StrongDual 𝕜 X) := inferInstance

@[reducible] noncomputable local instance prefixDualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 X) := inferInstance

namespace PrefixNormers

variable {f : ℕ → StrongDual 𝕜 X} (H : PrefixNormers f)

include H

lemma ambientPrefix_tendsto (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (x : closedSpan f) :
    Filter.Tendsto (fun m => H.ambientPrefix a ha hf m x) Filter.atTop
      (𝓝 (x : StrongDual 𝕜 X)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp x.property (ε / 4) (by positivity)
  let yc : closedSpan f := ⟨y, Submodule.le_topologicalClosure _ hy⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (H.ambientPrefix_eventually_span a ha hf ⟨y, hy⟩)
  refine ⟨N, fun m hm => ?_⟩
  have he := hN m hm
  have hb := H.ambientPrefix_bound a ha hf m (x - yc)
  change ‖H.ambientPrefix a ha hf m ((x : StrongDual 𝕜 X) - y)‖ ≤
    2 * ‖(x : StrongDual 𝕜 X) - y‖ at hb
  rw [map_sub, he] at hb
  rw [dist_eq_norm] at hxy ⊢
  calc
    ‖H.ambientPrefix a ha hf m x - (x : StrongDual 𝕜 X)‖ ≤
        ‖H.ambientPrefix a ha hf m x - y‖ + ‖y - (x : StrongDual 𝕜 X)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖(x : StrongDual 𝕜 X) - y‖ + ‖y - (x : StrongDual 𝕜 X)‖ :=
      add_le_add hb le_rfl
    _ < ε := by rw [norm_sub_rev y]; linarith

end PrefixNormers
end SeparableQuotient
end OAI
