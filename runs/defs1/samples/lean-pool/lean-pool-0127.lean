@[expose] public section

namespace ScottishBook155

namespace ProtectedChain

/-- Transport a target bidirectional system along equality of its protected
stage family. -/
noncomputable def transportTargetSystem {ι : Type} [LinearOrder ι]
    {r : ℝ} {S T : ι → ProtectedStage.{0} r} (h : S = T)
    (B : CoherentBiSystem (fun i => (S i).target)) :
    CoherentBiSystem (fun i => (T i).target) := by
  subst T
  exact B

end ProtectedChain
end ScottishBook155
end
