public section

open Filter Topology Pointwise

namespace TauCeti.Huber

variable {A : Type*} [CommRing A]

variable {A₀ : Subring A} {ϖ : Aˣ} {a : ℝ}

section Topology

variable [TopologicalSpace A]
  (hb : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True)
    (fun n ↦ {x | ((ϖ ^ (-(n : ℤ)) : Aˣ) : A) * x ∈ A₀}))

include hb

theorem hasBasis_tateGauge [SeparatelyContinuousMul A] (ha : 1 < a) (hϖ : (ϖ : A) ∈ A₀) :
    (𝓝 (0 : A)).HasBasis (fun ε : ℝ ↦ 0 < ε) (fun ε ↦ {x | tateGauge A₀ ϖ a x < ε}) := by
  refine hb.to_hasBasis (fun n _ ↦ ⟨a ^ (-(n : ℤ)), zpow_pos (zero_lt_one.trans ha) _,
    fun x hx ↦ (tateGauge_le_zpow_iff hϖ (exists_zpow_mul_mem_of_hasBasis hb x) ha).1
      (le_of_lt hx)⟩) fun ε hε ↦ ?_
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ ha)
  exact ⟨n, trivial, fun x hx ↦ (tateGauge_le_zpow (zero_le_one.trans ha.le) hx).trans_lt <|
    by simpa [zpow_neg] using hn⟩

end Topology
end TauCeti.Huber
end
