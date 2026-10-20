@[expose] public section

open CategoryTheory Set

universe u v

namespace ProfiniteGrp

theorem finiteCyclicGenerator_isTopologicalGenerator (n : ℕ) [NeZero n] :
    IsTopologicalGenerator (finiteCyclic n) (finiteCyclicGenerator n) := by
  apply Function.Surjective.denseRange
  intro x
  change Multiplicative (ZMod n) at x
  simp only [finiteCyclicGenerator]
  change ∃ k : ℤ, Multiplicative.ofAdd (1 : ZMod n) ^ k = x
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective x.toAdd
  refine ⟨k, Multiplicative.toAdd.injective ?_⟩
  simpa only [toAdd_zpow, toAdd_ofAdd, Int.smul_one_eq_cast] using hk

end ProfiniteGrp
end
