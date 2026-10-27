public section

noncomputable section

open NumberField

open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] (O : NumberFieldOrder K)

/-- **Extension and contraction away from the conductor.** Extending ideals from an order to
`𝓞 K` is a monoid isomorphism from the nonzero ideals of the order coprime to the conductor onto
the nonzero ideals of `𝓞 K` coprime to the conductor, whose inverse is contraction. -/
def integralIdealsAwayConductorEquiv :
    O.integralIdealsAwayConductor ≃* integralIdealsPrimeTo O.conductorModulus where
  toFun I := ⟨I.1.map (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K), by
    rw [mem_integralIdealsPrimeTo_conductorModulus_iff]
    refine ⟨fun h => I.2.1 ?_,
      map_sup_eq_top_of_coprime_comap (S := O.toRingOfIntegers.toSubring) I.2.2⟩
    exact (comap_map_of_coprime_comap (S := O.toRingOfIntegers.toSubring)
      O.conductor_le_toRingOfIntegers I.2.2).symm.trans
        ((congrArg (Ideal.comap O.toRingOfIntegers.toSubring.subtype) h).trans
          (Ideal.comap_bot_of_injective _ Subtype.val_injective))⟩
  invFun J := ⟨J.1.comap (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K), by
    have hJ := (O.mem_integralIdealsPrimeTo_conductorModulus_iff).mp J.2
    refine ⟨fun h => hJ.1 ?_, comap_sup_eq_top_of_le (S := O.toRingOfIntegers.toSubring)
      O.conductor_le_toRingOfIntegers hJ.2⟩
    exact (map_comap_of_coprime (S := O.toRingOfIntegers.toSubring)
      O.conductor_le_toRingOfIntegers hJ.2).symm.trans
        ((congrArg (Ideal.map O.toRingOfIntegers.toSubring.subtype) h).trans Ideal.map_bot)⟩
  left_inv I := Subtype.ext <|
    comap_map_of_coprime_comap (S := O.toRingOfIntegers.toSubring)
      O.conductor_le_toRingOfIntegers I.2.2
  right_inv J := Subtype.ext <|
    map_comap_of_coprime (S := O.toRingOfIntegers.toSubring)
      O.conductor_le_toRingOfIntegers ((O.mem_integralIdealsPrimeTo_conductorModulus_iff).mp J.2).2
  map_mul' I J := Subtype.ext (Ideal.map_mul _ _ _)

end NumberFieldOrder
end TauCeti.GlobalNumberFields
end
end
