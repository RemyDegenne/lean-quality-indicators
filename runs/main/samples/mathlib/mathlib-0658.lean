@[expose] public section

noncomputable section

open Set Function Filter Finset Metric Module Asymptotics Nat

open scoped Topology Ring

variable {α : Type*}

variable {R S : Type*} [Field R] [Field S] [LinearOrder S] {v w : AbsoluteValue R S}
  [TopologicalSpace S] [IsStrictOrderedRing S] [Archimedean S] [_i : OrderTopology S]

section NonUnitalNormedRing

variable {R : Type*} [NonUnitalNormedRing R]

protected theorem Summable.add_geom_series_mul_self {x : R} (h : Summable ((· * x)^[·] x)) :
    x + (∑' i : ℕ, (· * x)^[i] x) * x = (∑' i : ℕ, (· * x)^[i] x) := by
  rw [← h.tsum_mul_right, h.tsum_eq_zero_add]
  simp [iterate_succ_apply']

end NonUnitalNormedRing
end
end
