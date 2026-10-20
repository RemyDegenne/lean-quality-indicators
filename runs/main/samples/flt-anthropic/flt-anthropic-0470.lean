namespace P2MW.S_HaarQuotient_setLIntegral_withDensity_eq_inv_mul_setLIntegral_of_forall_lintegral_eq

set_option autoImplicit false

open MeasureTheory

open scoped ENNReal

open HaarQuotientSetLIntegralWithDensity in
theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (H : Subgroup G) (μH : Measure ↥H) [μH.IsMulRightInvariant]
    (ρ : G → ENNReal)
    (hquot : ∀ h : G → ENNReal, Measurable h →
      ∫⁻ g, h g ∂μ = ∫⁻ q, (∫⁻ x, h ((x : G) * q.out) ∂μH)
        ∂(Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) (μ.withDensity ρ)))
    (K : Subgroup G) (hK : IsClosed (K : Set G)) (t : G) (S : Set G) (hS : MeasurableSet S)
    (hmemS : ∀ g : G, g ∈ S ↔ ∃ x ∈ H, ∃ k ∈ K, g = x * t * k)
    (D : ENNReal) (hD : μH {y : ↥H | t⁻¹ * (y : G) * t ∈ K} = D) (hD0 : D ≠ 0) (hDtop : D ≠ ⊤)
    (f : G → ENNReal) (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) :
    ∫⁻ g in S, f g ∂(μ.withDensity ρ) = D⁻¹ * ∫⁻ k in (K : Set G), f (t * k) ∂μ := by
  have hKm : MeasurableSet (K : Set G) := hK.measurableSet

  have hSH : ∀ x ∈ H, ∀ g : G, x * g ∈ S ↔ g ∈ S := fun x hx g =>
    mul_mem_iff_of_doubleCoset H K t S hmemS hx g

  let F : MulAction.orbitRel.Quotient H G → ℝ≥0∞ := fun q => S.indicator f q.out
  have hFmk : ∀ g : G, F (Quotient.mk'' g) = S.indicator f g := by
    intro g
    obtain ⟨x, hx⟩ :=
      MulAction.orbitRel_apply.1 (Quotient.mk_out' (s₁ := MulAction.orbitRel H G) g)
    show S.indicator f ((Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out) = S.indicator f g
    rw [← hx]
    show S.indicator f ((x : G) * g) = S.indicator f g
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hSH x x.2 g).2 hg), hfH x x.2]
    · rw [Set.indicator_of_notMem hg,
        Set.indicator_of_notMem (fun h' => hg ((hSH x x.2 g).1 h'))]
  have hFm : Measurable F := by
    rw [measurable_from_quotient]
    have : F ∘ Quotient.mk'' = S.indicator f := funext hFmk
    rw [this]
    exact hf.indicator hS

  have hL : ∫⁻ g in S, f g ∂(μ.withDensity ρ) =
      ∫⁻ q, F q ∂(Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)
        (μ.withDensity ρ)) := by
    rw [lintegral_map hFm measurable_quotient_mk'', ← lintegral_indicator hS]
    exact lintegral_congr fun g => (hFmk g).symm

  let h : G → ℝ≥0∞ := fun g => ((fun g => t⁻¹ * g) ⁻¹' (K : Set G)).indicator f g
  have hhm : Measurable h := hf.indicator (hKm.preimage (measurable_const_mul _))

  have hR : ∫⁻ g, h g ∂μ = ∫⁻ k in (K : Set G), f (t * k) ∂μ := by
    rw [← lintegral_mul_left_eq_self _ t, ← lintegral_indicator hKm]
    refine lintegral_congr fun g => ?_
    show ((fun g => t⁻¹ * g) ⁻¹' (K : Set G)).indicator f (t * g) = (K : Set G).indicator _ g
    by_cases hg : g ∈ (K : Set G)
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem]
      show t⁻¹ * (t * g) ∈ (K : Set G)
      rwa [inv_mul_cancel_left]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem]
      show t⁻¹ * (t * g) ∉ (K : Set G)
      rwa [inv_mul_cancel_left]

  set A : Set ↥H := {y : ↥H | t⁻¹ * (y : G) * t ∈ K} with hA
  have hAm : MeasurableSet A :=
    hKm.preimage ((measurable_subtype_coe.const_mul _).mul_const _)

  have hinner : ∀ q : MulAction.orbitRel.Quotient H G,
      ∫⁻ x : ↥H, h ((x : G) * q.out) ∂μH = D * F q := by
    intro q
    by_cases hg₀ : q.out ∈ S
    · obtain ⟨x₀, hx₀, k₀, hk₀, hg₀e⟩ := (hmemS q.out).1 hg₀
      have hFq : F q = f q.out := Set.indicator_of_mem hg₀ f
      have hint : ∀ x : ↥H, h ((x : G) * q.out) =
          ((fun y : ↥H => y * ⟨x₀, hx₀⟩) ⁻¹' A).indicator (fun _ => f q.out) x := by
        intro x
        have hiff := mem_iff_of_eq_mul_mul K t hk₀ hg₀e (x : G)
        by_cases hc : t⁻¹ * ((x : G) * x₀) * t ∈ K
        · rw [Set.indicator_of_mem (show x ∈ (fun y : ↥H => y * ⟨x₀, hx₀⟩) ⁻¹' A from by
            simpa only [Set.mem_preimage, hA, Set.mem_setOf_eq, Subgroup.coe_mul] using hc)]
          show ((fun g => t⁻¹ * g) ⁻¹' (K : Set G)).indicator f ((x : G) * q.out) = f q.out
          rw [Set.indicator_of_mem (show (x : G) * q.out ∈ (fun g => t⁻¹ * g) ⁻¹' (K : Set G) from
            hiff.2 hc), hfH x x.2]
        · rw [Set.indicator_of_notMem (show x ∉ (fun y : ↥H => y * ⟨x₀, hx₀⟩) ⁻¹' A from by
            simpa only [Set.mem_preimage, hA, Set.mem_setOf_eq, Subgroup.coe_mul] using hc)]
          exact Set.indicator_of_notMem
            (show (x : G) * q.out ∉ (fun g => t⁻¹ * g) ⁻¹' (K : Set G) from fun h' => hc (hiff.1 h')) _
      have hmeas : MeasurableSet ((fun y : ↥H => y * ⟨x₀, hx₀⟩) ⁻¹' A) :=
        (measurable_id.mul_const _) hAm
      rw [hFq, lintegral_congr hint, lintegral_indicator_const hmeas,
        measure_preimage_mul_right, hD, mul_comm]
    · have hFq : F q = 0 := Set.indicator_of_notMem hg₀ f
      have hint : ∀ x : ↥H, h ((x : G) * q.out) = 0 := fun x =>
        Set.indicator_of_notMem
          (show (x : G) * q.out ∉ (fun g => t⁻¹ * g) ⁻¹' (K : Set G) from
            not_mem_of_not_mem_doubleCoset H K t S hmemS hg₀ x.2) _
      rw [hFq, mul_zero, lintegral_congr hint, lintegral_zero]

  have key : ∫⁻ k in (K : Set G), f (t * k) ∂μ = D * ∫⁻ g in S, f g ∂(μ.withDensity ρ) := by
    rw [← hR, hquot h hhm, hL, ← lintegral_const_mul' _ _ hDtop]
    exact lintegral_congr hinner
  rw [key, ← mul_assoc, ENNReal.inv_mul_cancel hD0 hDtop, one_mul]

end P2MW.S_HaarQuotient_setLIntegral_withDensity_eq_inv_mul_setLIntegral_of_forall_lintegral_eq
