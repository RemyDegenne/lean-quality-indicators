public section

noncomputable section

open ValuativeRel

namespace TauCeti

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

variable (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [FiniteDimensional K L]

@[simp]
theorem localNormQuotientEquivZModOfUnramified_mk (h : ramificationIndex K L = 1) (x : Kˣ) :
    localNormQuotientEquivZModOfUnramified K L h (Additive.ofMul (QuotientGroup.mk x)) =
      normalizedValuationMod K (Module.finrank K L) (Additive.ofMul x) := by
  have : IsUnramified K L := (isUnramified_iff_ramificationIndex_eq_one K L).2 h
  -- Expose the additive and multiplicative type tags so the two quotient-equivalence evaluation
  -- lemmas apply without unfolding their noncomputable first-isomorphism constructions.
  change Multiplicative.toAdd
    (((QuotientGroup.quotientMulEquivOfEq (normGroup_eq_ker_normalizedValuationMod K L)).trans
        (QuotientGroup.quotientKerEquivOfSurjective _
          (normalizedValuationModMul_surjective K (Module.finrank K L))))
      (QuotientGroup.mk x)) = _
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk]
  rfl

end TauCeti
end
end
