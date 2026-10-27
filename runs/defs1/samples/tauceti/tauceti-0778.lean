public section

open scoped Pointwise

namespace TauCeti

namespace Place

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}

variable [Field k] [Field F] [Field F']

variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']

section Residue

variable (F) (P : Place k F') {t : F'}

/-- **The ramification residue** (Stichtenoth, Proposition 3.8.5): for a uniformizer `t` at `P`,
the map sending an automorphism `σ` of `G_{i+1}(P)` to the function `z ↦ ((σ z - z)/t^{i+2})(P)`
on `𝒪_P`.  It is a homomorphism into the *additive* group of functions `𝒪_P → F'_P`, which is
therefore written multiplicatively here.  The map depends on the choice of `t`; its kernel,
`TauCeti.Place.ker_ramificationResidueHom`, does not. -/
noncomputable def ramificationResidueHom (ht : P.ord t = 1) (i : ℕ) :
    ramificationGroup F P (i + 1) →* Multiplicative (P.integers → P.ResidueField) :=
  MonoidHom.mk'
    (fun g ↦ Multiplicative.ofAdd fun x ↦
      filtrationResidue (P := P) (a := (i : ℤ) + 2) (s := (t ^ (i + 2))⁻¹)
        (ord_inv_pow_add_two P ht i) ⟨_, sub_mem_filtration_add_two F P g x.2⟩)
    (by
      intro g h
      rw [← ofAdd_add]
      refine congrArg Multiplicative.ofAdd (funext fun x ↦ ?_)
      have ht0 : t ≠ 0 := fun h0 ↦ by simp [h0, ord_zero] at ht
      set s : F' := (t ^ (i + 2))⁻¹ with hs
      set σ : F' ≃ₐ[F] F' := ((g : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F')
      set τ : F' ≃ₐ[F] F' := ((h : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F')
      -- Normalize the error of `τ` by the chosen power of the uniformizer.
      have hw : τ (x : F') - (x : F') ∈ P.filtration ((i : ℤ) + 2) :=
        sub_mem_filtration_add_two F P h x.2
      have hc : s * (τ (x : F') - (x : F')) ∈ P.integers :=
        mul_mem_integers_of_mem_filtration (ord_inv_pow_add_two P ht i) hw
      set c : F' := s * (τ (x : F') - (x : F')) with hcdef
      have hwc : τ (x : F') - (x : F') = t ^ (i + 2) * c := by
        rw [hcdef, hs, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht0), one_mul]
      have htmem : t ∈ P.integers := by
        rw [mem_integers_iff_ord_nonneg, ht]
        norm_num
      have hσt : σ t - t ∈ P.filtration ((i : ℤ) + 2) := sub_mem_filtration_add_two F P g htmem
      set u : F' := σ t * t⁻¹ with hu
      have hu1 : u - 1 ∈ P.filtration 1 := by
        -- Rewrite the uniformizer ratio so its filtration follows from `σ t - t`.
        rw [show u - 1 = (σ t - t) * t⁻¹ by rw [hu]; field_simp]
        have hord : P.ord t⁻¹ = -1 := by rw [ord_inv, ht]
        have h2 : (2 : ℤ) ≤ (i : ℤ) + 2 := by omega
        have h3 := P.mul_mem_filtration (P.filtration_antitone h2 hσt)
          (P.mem_filtration_ord t⁻¹)
        -- The filtration indices add to `2 + (-1) = 1`.
        rwa [hord, show (2 : ℤ) + -1 = 1 by ring] at h3
      have humem : u ∈ P.integers := by
        -- Recover integrality of `u` from the integral summands `u - 1` and `1`.
        rw [show u = (u - 1) + 1 by ring]
        have h0 : (0 : ℤ) ≤ 1 := by norm_num
        exact add_mem (P.mem_filtration_zero_iff.mp (P.filtration_antitone h0 hu1)) (one_mem _)
      have hσc : σ c - c ∈ P.filtration 1 := by
        have h1 := g.2 c hc
        have h2 : (1 : ℤ) ≤ ((i + 1 : ℕ) : ℤ) + 1 := by push_cast; omega
        exact P.filtration_antitone h2 h1
      have hσcmem : σ c ∈ P.integers := (mem_integers_decompositionSubgroup_apply F P _).mpr hc
      -- Expand the composite-action error using `σ t = u * t`.
      have hexp : s * (σ (τ (x : F')) - σ (x : F')) = u ^ (i + 2) * σ c := by
        rw [← map_sub, hwc, map_mul, map_pow, hu, mul_pow, inv_pow, hs]
        ring
      have hkey : s * (σ (τ (x : F')) - σ (x : F')) - c ∈ P.filtration 1 := by
        -- Separate the two error terms: `u^(i+2) - 1` and `σ c - c`.
        rw [hexp, show u ^ (i + 2) * σ c - c = (u ^ (i + 2) - 1) * σ c + (σ c - c) by ring]
        refine Submodule.add_mem _ ?_ hσc
        simpa using P.mul_mem_filtration (P.pow_sub_one_mem_filtration humem hu1 (i + 2))
          (P.mem_filtration_zero_iff.mpr hσcmem)
      simp only [Pi.add_apply, filtrationResidue_apply, ← map_add]
      refine (P.residue_eq_iff_sub_mem_filtration_one).mpr ?_
      convert hkey using 1
      -- Unfold the three residue numerators to the field identity supplied by `hkey`.
      change s * (σ (τ (x : F')) - (x : F')) -
          (s * (σ (x : F') - (x : F')) + s * (τ (x : F') - (x : F'))) =
        s * (σ (τ (x : F')) - σ (x : F')) - c
      rw [hcdef]
      ring)

end Residue
end Place
end TauCeti
end
