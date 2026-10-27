namespace P2MW.S_NumberField_PlaceDecomp_exists_unit_inflate_map_delta_res_eq_kummer_cup_localBridge_of_isLevelConstant

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 6400000

open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation

open scoped NumberField.PlaceDecomp

namespace BridgeCup

noncomputable scoped instance divisibleBy_additive_units (K : Type) [Field K] [IsAlgClosed K] :
    DivisibleBy (Additive Kˣ) ℤ :=
  divisibleByOfSMulRightSurj (Additive Kˣ) ℤ fun {n} hn a => by
    have hk : 0 < n.natAbs := Int.natAbs_pos.2 hn
    obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul a : Kˣ) : K) hk
    have hv0 : v ≠ 0 := fun h0 => (Additive.toMul a).ne_zero (by rw [← hv, h0, zero_pow hk.ne'])
    have hw : (Units.mk0 v hv0) ^ n.natAbs = Additive.toMul a := Units.ext (by simp [hv])
    rcases Int.natAbs_eq n with h | h
    · refine ⟨Additive.ofMul (Units.mk0 v hv0), ?_⟩
      change Additive.ofMul ((Units.mk0 v hv0) ^ n) = a
      rw [h, zpow_natCast, hw]
      rfl
    · refine ⟨Additive.ofMul (Units.mk0 v hv0)⁻¹, ?_⟩
      change Additive.ofMul ((Units.mk0 v hv0)⁻¹ ^ n) = a
      rw [h, zpow_neg, inv_zpow, inv_inv, zpow_natCast, hw]
      rfl

universe u

variable {k : Type u} [Field k] {Γ H : Type u} [Group Γ] [Group H] (loc : H →* Γ) (M : Rep.{u} k Γ) (χ : Γ →* kˣ)

section KumMap

variable {p : ℕ} [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (q : Nat.Primes) [Fact ((q : ℕ)).Prime]

noncomputable def zetaq : (PadicAlgCl q)ˣ :=
  Units.mk0 (padicEmbedding q ζ) (by
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    exact (hζ.map_of_injective (padicEmbedding (q : ℕ)).toRingHom.injective).ne_zero (Fact.out : p.Prime).ne_zero)

end KumMap
end BridgeCup
end P2MW.S_NumberField_PlaceDecomp_exists_unit_inflate_map_delta_res_eq_kummer_cup_localBridge_of_isLevelConstant
