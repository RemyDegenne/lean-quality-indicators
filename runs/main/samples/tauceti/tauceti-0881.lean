public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B} {b : B}

lemma normalizerQuotient_one_smul_subgroupFiberOrbitClass (H : Subgroup (deck p)) (e : p ⁻¹' {b}) :
    (1 : Subgroup.normalizerQuotient H) • subgroupFiberOrbitClass H e =
      subgroupFiberOrbitClass H e := by
  simp

end Deck
end TauCeti
end
