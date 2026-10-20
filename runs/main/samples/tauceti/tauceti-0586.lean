public section

namespace TauCeti

namespace ValidLieTypeIndex

open LieTypeIndex (usesHalfFrobenius_iff)

noncomputable section

section Branches

variable {n m : ℕ} {q : PrimePower}

theorem simpleRootSubgroup_reeG2 (hv : (LieTypeIndex.reeG2 m).Valid) :
    simpleRootSubgroup ⟨_, hv⟩ = (ReeG2LieIndex.of m hv).simpleRootSubgroup :=
  (rfl)

end Branches
end
end ValidLieTypeIndex
end TauCeti
end
