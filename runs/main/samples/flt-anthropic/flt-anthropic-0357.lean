namespace P2MW.S_ModularCurve_UVCrossingModel_exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot_mul

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

namespace KummerClass44

open KummerNorm44

section K4Residue

variable {W : Type*} [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W]
  [HenselianRing W (IsLocalRing.maximalIdeal W)]

theorem exists_eq_const_of_pow_eq_const (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W)
    [IsLocalRing (UVCrossingModel W c)]
    (n : ℕ) (hn : 0 < n) (hnW : IsUnit (n : W)) (ζ : W) (hζ : IsPrimitiveRoot ζ n)
    (d : ℕ) (hd : d ∣ n)
    (F : Type*) [Field F] [Algebra (UVCrossingModel W c) F]
    (hinj : Function.Injective (algebraMap (UVCrossingModel W c) F))
    [IsLocalRing ↥(integralClosure (UVCrossingModel W c) F)]
    (hres : ∀ b : ↥(integralClosure (UVCrossingModel W c) F), ∃ w : W,
      b - algebraMap (UVCrossingModel W c) _ (const c w) ∈
        IsLocalRing.maximalIdeal ↥(integralClosure (UVCrossingModel W c) F))
    (w : W) (hw : IsUnit w) (ε : F) (hε : ε ^ d = algebraMap (UVCrossingModel W c) F (const c w)) :
    ∃ w₁ : W, ε = algebraMap (UVCrossingModel W c) F (const c w₁) := by
  classical
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hn

  have hdW : IsUnit (d : W) := by
    obtain ⟨e, he⟩ := hd
    have : (n : W) = (d : W) * (e : W) := by rw [he, Nat.cast_mul]
    rw [this] at hnW
    exact isUnit_of_mul_isUnit_left hnW

  have hεint : IsIntegral (UVCrossingModel W c) ε := by
    refine ⟨Polynomial.X ^ d - Polynomial.C (const c w), Polynomial.monic_X_pow_sub_C _ hd0.ne', ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hε, sub_self]
  have hεmem : ε ∈ integralClosure (UVCrossingModel W c) F := hεint
  obtain ⟨w', hw'⟩ := hres ⟨ε, hεmem⟩

  have h1 : (⟨ε, hεmem⟩ : ↥(integralClosure (UVCrossingModel W c) F)) ^ d =
      algebraMap (UVCrossingModel W c) _ (const c w) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, Subalgebra.coe_algebraMap]
    exact hε
  have hmemB : algebraMap (UVCrossingModel W c) ↥(integralClosure (UVCrossingModel W c) F)
      (const c (w - w' ^ d)) ∈
        IsLocalRing.maximalIdeal ↥(integralClosure (UVCrossingModel W c) F) := by
    obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow
      (⟨ε, hεmem⟩ : ↥(integralClosure (UVCrossingModel W c) F))
      (algebraMap (UVCrossingModel W c) _ (const c w')) d
    have h2 : algebraMap (UVCrossingModel W c) ↥(integralClosure (UVCrossingModel W c) F)
        (const c (w - w' ^ d)) =
        (⟨ε, hεmem⟩ : ↥(integralClosure (UVCrossingModel W c) F)) ^ d -
          (algebraMap (UVCrossingModel W c) _ (const c w')) ^ d := by
      rw [← constHom_apply, map_sub, map_pow, map_sub, map_pow, constHom_apply, constHom_apply, h1]
    rw [h2, hq]
    exact Ideal.mul_mem_right _ _ hw'

  have hmW : w - w' ^ d ∈ IsLocalRing.maximalIdeal W := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← isUnit_const_iff c hc]
    intro hu
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hmemB (hu.map _))

  have hw'u : IsUnit w' := by
    by_contra h
    have h' : w' ^ d ∈ IsLocalRing.maximalIdeal W :=
      Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr h) _ hd0
    have hwm : w ∈ IsLocalRing.maximalIdeal W := by
      have := Ideal.add_mem _ hmW h'
      rwa [sub_add_cancel] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp hwm hw

  obtain ⟨v, hv⟩ := hw'u.exists_right_inv
  have ha : w * v ^ d - 1 ∈ IsLocalRing.maximalIdeal W := by
    have : w * v ^ d - 1 = (w - w' ^ d) * v ^ d := by
      rw [sub_mul, ← mul_pow, hv, one_pow]
    rw [this]
    exact Ideal.mul_mem_right _ _ hmW
  obtain ⟨ω, hωu, hω⟩ := exists_isUnit_pow_eq d hdW _ ha
  have hw1 : (w' * ω) ^ d = w := by
    calc (w' * ω) ^ d = w * (w' * v) ^ d := by rw [mul_pow, hω, mul_pow]; ring
      _ = w := by rw [hv, one_pow, mul_one]

  set f : W →+* F := (algebraMap (UVCrossingModel W c) F).comp (constHom c) with hfdef
  have hfinj : Function.Injective f := hinj.comp (const_injective c hc)
  have hfw : f (w' * ω) ≠ 0 := (map_ne_zero_iff f hfinj).mpr (hw'u.mul hωu).ne_zero
  have hfw' : f w ≠ 0 := (map_ne_zero_iff f hfinj).mpr hw.ne_zero
  have hε' : ε ^ d = f w := hε
  have hη : (ε / f (w' * ω)) ^ d = 1 := by
    rw [div_pow, ← map_pow, hw1, hε', div_self hfw']
  obtain ⟨i, hi⟩ := exists_eq_pow_of_pow_eq_one' f hfinj ζ n hn hζ d hd _ hη
  refine ⟨ζ ^ (n / d * i) * (w' * ω), ?_⟩
  rw [div_eq_iff hfw] at hi
  rw [hi, ← map_mul]
  rfl

end K4Residue
end KummerClass44
end P2MW.S_ModularCurve_UVCrossingModel_exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot_mul
