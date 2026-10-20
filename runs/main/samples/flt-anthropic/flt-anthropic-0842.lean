namespace P2MW.S_IsDiscreteValuationRing_exists_finset_card_le_forall_exists_sub_mul_finprod_smul_mem_pow_of_prime_card

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxSynthPendingDepth 3

section GRINJ

namespace IsDiscreteValuationRing

namespace XCGrCoker

p2m_open

p2m_open

section jumpcases

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

variable {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]

variable [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]

variable [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]

theorem exists_finset_of_eq_jump_wild (hℓ : (Nat.card G).Prime) (t : ℕ) (ht1 : 1 ≤ t)
    (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤) (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    [Finite (B ⧸ IsLocalRing.maximalIdeal B)] :
    ∃ S : Finset B, S.card ≤ Nat.card G ∧
      (∀ s ∈ S, IsUnit s ∧ (∀ σ : G, σ • s = s) ∧ s - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * t)) ∧
      ∀ a : B, IsUnit a → (∀ σ : G, σ • a = a) → a - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * t) →
        ∃ s ∈ S, ∃ b : B, IsUnit b ∧ b - 1 ∈ IsLocalRing.maximalIdeal B ^ t ∧
          a - s * ∏ᶠ σ : G, σ • b ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * (t + 1)) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  let A := FixedPoints.subring B G
  haveI : IsDiscreteValuationRing A := FixedPoints.isDiscreteValuationRing_subring
  letI : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  letI : Field (B ⧸ IsLocalRing.maximalIdeal B) := Ideal.Quotient.field _
  haveI : Finite (A ⧸ IsLocalRing.maximalIdeal A) :=
    Finite.of_injective _ (algebraMap (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ IsLocalRing.maximalIdeal B)).injective

  have hℓB : (Nat.card G : B) ∈ IsLocalRing.maximalIdeal B := natCast_card_mem_maximalIdeal hℓ ht1 ht
  have hℓA : (Nat.card G : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [FixedPoints.mem_maximalIdeal_subring_iff]; push_cast; exact hℓB
  have hℓk : ((Nat.card G : ℕ) : A ⧸ IsLocalRing.maximalIdeal A) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)), Ideal.Quotient.eq_zero_iff_mem]
    exact hℓA
  haveI := Fact.mk hℓ
  haveI : CharP (A ⧸ IsLocalRing.maximalIdeal A) (Nat.card G) :=
    ringChar.eq_iff.mp (CharP.ringChar_of_prime_eq_zero hℓ hℓk)

  obtain ⟨π, ϖ, hπ, hϖG, hϖdef, hϖm, hdiv⟩ := exists_uniformizer_package (B := B) (G := G) ht
  have hπm : π ∈ IsLocalRing.maximalIdeal B := hπ.not_isUnit
  have hϖy : ∀ y : ℕ, ϖ ^ y ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * y) := fun y => by
    have := Ideal.pow_mem_pow hϖm y; rwa [← pow_mul] at this
  have hϖ1 : ϖ ∈ IsLocalRing.maximalIdeal B := Ideal.pow_le_self hℓ.ne_zero hϖm
  have hTrG : ∀ τ : G, τ • ∑ᶠ σ : G, σ • π ^ t = ∑ᶠ σ : G, σ • π ^ t := fun τ => smul_finsum_smul τ (π ^ t)
  have hTrm : ∑ᶠ σ : G, σ • π ^ t ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * t) :=
    finsum_smul_mem_of_mem_pow_jump hℓ t ht1 ht ht' (π ^ t) (Ideal.pow_mem_pow hπm t)
  obtain ⟨c, hcG, hTrc⟩ := hdiv t _ hTrG hTrm
  let cA : A := ⟨c, hcG⟩

  obtain ⟨f, hf, hker⟩ := card_ker_frobenius_add_le (k := A ⧸ IsLocalRing.maximalIdeal A) hℓ (Ideal.Quotient.mk _ cA)
  obtain ⟨T, hTcard, hT⟩ := exists_finset_reps_of_card_ker_le f (Nat.card G) hker
  have hL : ∀ ξ : A ⧸ IsLocalRing.maximalIdeal A, ∃ r : A, Ideal.Quotient.mk _ r = ξ := Ideal.Quotient.mk_surjective
  choose L hL using hL
  refine ⟨T.image (fun ξ => 1 + ϖ ^ t * (L ξ : B)), Finset.card_image_le.trans hTcard, ?_, ?_⟩
  · intro s hs
    obtain ⟨ξ, -, rfl⟩ := Finset.mem_image.mp hs
    refine ⟨isUnit_one_add_of_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hϖ1 t ht1)), fun σ => ?_, ?_⟩
    · rw [smul_add, smul_one, smul_mul', smul_pow', hϖG, (L ξ).2]
    · rw [add_sub_cancel_left]; exact Ideal.mul_mem_right _ _ (hϖy t)
  · intro a hau haG ha
    obtain ⟨β, hβG, hαβ⟩ := hdiv t (a - 1) (fun σ => by rw [smul_sub, haG, smul_one]) ha
    let βA : A := ⟨β, hβG⟩
    obtain ⟨r, hrT, ubar, hrep⟩ := hT (Ideal.Quotient.mk _ βA)
    obtain ⟨uA, huA⟩ := Ideal.Quotient.mk_surjective ubar
    set x : B := (uA : B) * π ^ t with hxdef
    have hxm : x ∈ IsLocalRing.maximalIdeal B ^ t := Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hπm t)
    have hx1 : x ∈ IsLocalRing.maximalIdeal B := Ideal.pow_le_self (by omega) hxm
    refine ⟨1 + ϖ ^ t * (L r : B), Finset.mem_image_of_mem _ hrT, 1 + x, isUnit_one_add_of_mem hx1,
      by rw [add_sub_cancel_left]; exact hxm, ?_⟩
    have hN1x : (∏ᶠ σ : G, σ • (1 + x)) = ∏ᶠ σ : G, (1 + σ • x) :=
      finprod_congr fun σ => by rw [smul_add, smul_one]
    have hcore := finprod_one_add_smul_sub_one_sub_finsum_sub_finprod_mem hℓ t ht1 ht ht' x hxm
    have hTrx : ∑ᶠ σ : G, σ • x = (uA : B) * (ϖ ^ t * c) := by
      rw [hxdef, finsum_smul_mul_of_forall_smul_eq uA.2 (π ^ t), hTrc]
    have hNx : ∏ᶠ σ : G, σ • x = (uA : B) ^ Nat.card G * ϖ ^ t := by
      rw [hxdef, finprod_smul_mul, finprod_smul_of_forall_smul_eq uA.2, hϖdef]
      congr 1
      simp only [finprod_eq_prod_of_fintype, smul_pow', Finset.prod_pow]

    have key : a - (1 + ϖ ^ t * (L r : B)) * ∏ᶠ σ : G, σ • (1 + x) =
        ϖ ^ t * (β - (L r : B) - c * (uA : B) - (uA : B) ^ Nat.card G)
          - ϖ ^ t * ϖ ^ t * ((L r : B) * (c * (uA : B) + (uA : B) ^ Nat.card G))
          - (1 + ϖ ^ t * (L r : B)) * ((∏ᶠ σ : G, (1 + σ • x)) - 1 - ∑ᶠ σ : G, σ • x - ∏ᶠ σ : G, σ • x) := by
      rw [hN1x]
      have ha1 : a = 1 + ϖ ^ t * β := by rw [← hαβ]; ring
      rw [ha1, hTrx, hNx]; ring
    rw [key]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) (Ideal.mul_mem_left _ _ hcore)
    ·
      have hδA : (βA - L r - cA * uA - uA ^ Nat.card G : A) ∈ IsLocalRing.maximalIdeal A := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        simp only [map_sub, map_mul, map_pow, hL r, huA, hrep, hf]
        ring
      have hδB := mem_maximalIdeal_pow_card_of_forall_smul_eq (G := G) ht
        (x := ((βA - L r - cA * uA - uA ^ Nat.card G : A) : B)) (βA - L r - cA * uA - uA ^ Nat.card G).2
        (FixedPoints.mem_maximalIdeal_subring_iff.mp hδA)
      have hδB' : β - (L r : B) - c * (uA : B) - (uA : B) ^ Nat.card G ∈ IsLocalRing.maximalIdeal B ^ Nat.card G := by
        simpa using hδB
      rw [Nat.mul_succ, pow_add]
      exact Ideal.mul_mem_mul (hϖy t) hδB'
    · refine Ideal.mul_mem_right _ _ ?_
      have h2 : ϖ ^ t * ϖ ^ t ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * t + Nat.card G * t) := by
        rw [pow_add]; exact Ideal.mul_mem_mul (hϖy t) (hϖy t)
      exact Ideal.pow_le_pow_right (by nlinarith) h2

end jumpcases
end XCGrCoker
end IsDiscreteValuationRing
end GRINJ
end P2MW.S_IsDiscreteValuationRing_exists_finset_card_le_forall_exists_sub_mul_finprod_smul_mem_pow_of_prime_card
