namespace P2MW.S_Algebra_Etale_eq_of_forall_algHom_apply_eq

set_option maxHeartbeats 3200000

universe u v w

namespace W2G9

section RangeRealization

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]

variable {L : Type*} [CommRing L] [Algebra K L]

variable {M : Type*} [Field M] [Algebra K M]

noncomputable def homOfRangeLe (χ : M →ₐ[K] Ω) (β : L →ₐ[K] Ω)
    (h : ∀ x, ∃ y, χ y = β x) : L →ₐ[K] M where
  toFun x := (h x).choose
  map_one' := χ.toRingHom.injective
    (show χ (h 1).choose = χ 1 from
      ((h 1).choose_spec.trans (map_one β)).trans (map_one χ).symm)
  map_mul' x y := χ.toRingHom.injective
    (show χ (h (x * y)).choose = χ ((h x).choose * (h y).choose) from
      (((h (x * y)).choose_spec.trans (map_mul β x y)).trans
        (congrArg₂ (· * ·) (h x).choose_spec.symm (h y).choose_spec.symm)).trans
        (map_mul χ _ _).symm)
  map_zero' := χ.toRingHom.injective
    (show χ (h 0).choose = χ 0 from
      ((h 0).choose_spec.trans (map_zero β)).trans (map_zero χ).symm)
  map_add' x y := χ.toRingHom.injective
    (show χ (h (x + y)).choose = χ ((h x).choose + (h y).choose) from
      (((h (x + y)).choose_spec.trans (map_add β x y)).trans
        (congrArg₂ (· + ·) (h x).choose_spec.symm (h y).choose_spec.symm)).trans
        (map_add χ _ _).symm)
  commutes' r := χ.toRingHom.injective
    (show χ (h (algebraMap K L r)).choose = χ (algebraMap K M r) from
      ((h (algebraMap K L r)).choose_spec.trans (β.commutes r)).trans (χ.commutes r).symm)

end RangeRealization
end W2G9
end P2MW.S_Algebra_Etale_eq_of_forall_algHom_apply_eq
