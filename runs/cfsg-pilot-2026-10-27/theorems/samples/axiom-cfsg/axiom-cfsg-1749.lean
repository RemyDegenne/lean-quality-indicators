public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZB

section Subgroups

variable {G : Type*} [Group G] [Finite G] {R : Subgroup G}

theorem exists_decomp_in_subgroup (hodd : Odd (Nat.card R)) {a : G} (ha : a ∈ R)
    (hac : ∀ r ∈ R, r * a = a * r) {σ τ : G} (hσ : σ * σ = 1) (hτ : τ * τ = 1)
    (hσR : ∀ r ∈ R, σ * r * σ⁻¹ ∈ R) (hτR : ∀ r ∈ R, τ * r * τ⁻¹ ∈ R)
    (hσa : σ * a * σ⁻¹ = a) (hτa : τ * a * τ⁻¹ = a)
    (hinv : ∀ r ∈ R, ∃ j : ℤ, (σ * τ) * r * (σ * τ)⁻¹ = r⁻¹ * a ^ j) {r : G} (hr : r ∈ R) :
    ∃ r₁ ∈ R, ∃ r₂ ∈ R, ∃ j : ℤ, σ * r₁ * σ⁻¹ = r₁ ∧ τ * r₂ * τ⁻¹ = r₂ ∧
      r = r₁ * r₂ * a ^ j := by
  classical
  let a' : R := ⟨a, ha⟩
  let σ' : R ≃* R := conjAut σ hσ hσR
  let τ' : R ≃* R := conjAut τ hτ hτR
  let Z : Subgroup R := Subgroup.zpowers a'
  have hZc : Z ≤ Subgroup.center R := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    exact fun g => Subtype.ext (hac g g.2)
  have hσ'Z : ∀ z ∈ Z, σ' z = z := by
    rintro _ ⟨k, rfl⟩
    rw [map_zpow, show σ' a' = a' from Subtype.ext hσa]
  have hτ'Z : ∀ z ∈ Z, τ' z = z := by
    rintro _ ⟨k, rfl⟩
    rw [map_zpow, show τ' a' = a' from Subtype.ext hτa]
  have hsq : ∀ (u : G) (hu : u * u = 1) (hR : ∀ r ∈ R, u * r * u⁻¹ ∈ R) (x : R),
      conjAut u hu hR (conjAut u hu hR x) = x := by
    intro u hu hR x
    apply Subtype.ext
    have h : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
    show u * (u * (x : G) * u⁻¹) * u⁻¹ = x
    rw [h]
    calc u * (u * (x : G) * u) * u = (u * u) * x * (u * u) := by group
      _ = x := by rw [hu]; group
  have hinv' : ∀ x : R, ∃ z ∈ Z, σ' (τ' x) = x⁻¹ * z := by
    intro x
    obtain ⟨j, hj⟩ := hinv x x.2
    refine ⟨a' ^ j, ⟨j, rfl⟩, Subtype.ext ?_⟩
    show σ * (τ * (x : G) * τ⁻¹) * σ⁻¹ = (x : G)⁻¹ * a ^ j
    rw [← hj]
    group
  obtain ⟨x₁, x₂, z, hz, h1, h2, h3⟩ := exists_decomp_of_inverting hodd hZc σ' τ'
    (hsq σ hσ hσR) (hsq τ hτ hτR) (fun z hz => by rw [hσ'Z z hz]; exact hz)
    (fun z hz => by rw [hτ'Z z hz]; exact hz) hinv' ⟨r, hr⟩
  obtain ⟨j, hj⟩ := hz
  refine ⟨x₁, x₁.2, x₂, x₂.2, j, congrArg Subtype.val h1, congrArg Subtype.val h2, ?_⟩
  have h4 := congrArg Subtype.val h3
  rw [← hj] at h4
  simpa [a'] using h4

end Subgroups
end CFSG.ClassicalInvolution.Q3.Q3ZB
end
