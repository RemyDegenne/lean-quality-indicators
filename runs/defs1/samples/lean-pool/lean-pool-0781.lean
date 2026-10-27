@[expose] public section

noncomputable section

namespace NavierStokes.PrimaryFieldAssembly

open Set Function PartitionedCovariance HarmonicCalculus

open scoped BigOperators Topology

variable {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt}

section Source

open PrimaryPulseBounds

variable {Q : Type} [NormedAddCommGroup Q]

namespace SourcePair

variable {U : UnsignedLabel} (A : SourcePair Q sys U)

/-- Pair data, bundling `pulses`, `ci`, `ci_pos`, `fits` and the required compatibility proofs. -/
noncomputable def pairData : PairData sys U where
  pulses := fun j => canonicalPrimaryPulse (A.frame j) (A.lam j) (A.rate j)
    (A.length_pos j) A.domain (A.coefficient_continuous j) A.point A.point_mem (A.kinematics j)
  ci := A.stretch
  ci_pos := A.stretch_pos
  fits := by
    intro j t ht
    have hmem : t ∈ Icc 0 (A.length j) := by
      by_contra hn
      exact ht (slotCutoff_zero_of_not_mem_Icc (A.length_pos j) hn)
    exact ⟨hmem.1, hmem.2.trans (A.fits j)⟩
  modes := A.mode
  modes_ne := A.mode_ne
  phases := A.phase

end SourcePair
end Source
end NavierStokes.PrimaryFieldAssembly
end
end
