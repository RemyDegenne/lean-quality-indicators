public section

open Set Topology

namespace ContinuousMap

variable {A B X : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]

theorem isInducing_precomp_of_surjective [CompactSpace A] [T2Space B] (q : C(A, B))
    (hq : Function.Surjective q) :
    IsInducing (fun f : C(B, X) => f.comp q) := by
  refine ⟨le_antisymm (continuous_iff_le_induced.mp (continuous_precomp q)) ?_⟩
  refine le_generateFrom ?_
  rintro _ ⟨K, hK, U, hU, rfl⟩
  have hpre : IsOpen {g : C(A, X) | MapsTo g (q ⁻¹' K) U} :=
    isOpen_setOfPred_mapsTo ((hK.isClosed.preimage q.continuous).isCompact) hU
  refine ⟨_, hpre, ?_⟩
  ext f
  constructor
  · intro h b hb
    obtain ⟨a, rfl⟩ := hq b
    exact h hb
  · intro h a ha
    exact h ha

end ContinuousMap
end
