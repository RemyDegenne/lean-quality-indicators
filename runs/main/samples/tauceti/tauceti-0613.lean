public noncomputable section

namespace TauCeti

open Function Set Topology ThricePuncturedSphere PunctureFilling

open scoped ContDiff Manifold OnePoint

namespace AnalyticBelyiPair

@[simp]
theorem isoClassEquivConnectedCoverClass_symm_apply {n : ℕ}
    (c : ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    (isoClassEquivConnectedCoverClass n).symm c = c.toAnalyticBelyiPair :=
  (rfl)

end AnalyticBelyiPair
end TauCeti
end
