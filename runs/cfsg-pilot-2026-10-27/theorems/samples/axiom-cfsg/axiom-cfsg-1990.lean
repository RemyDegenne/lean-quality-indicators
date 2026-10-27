public noncomputable section

namespace CFSG.Wreathed.BaseFourCentralizerStructure

open scoped Classical Pointwise

universe u

variable {G : Type u} [Group G]

@[simp] theorem originalBaseToFourNormalizerQuotientEquiv_mk [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelBase S e : Set G)) :
    originalBaseToFourNormalizerQuotientEquiv n hn S e
      ((QuotientGroup.mk' _) g) =
        (QuotientGroup.mk' _)
          (Subgroup.inclusion (modelBase_normalizer_le_modelT_normalizer n (by omega) S e) g) :=
  QuotientGroup.liftEquiv_mk _ _ _ g

end CFSG.Wreathed.BaseFourCentralizerStructure
end
