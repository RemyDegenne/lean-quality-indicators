namespace OAI

open scoped BigOperators

namespace CartierSections

section AlgebraicDegree

variable {ι k J : Type*} [Fintype ι] [CommRing k]

theorem algebraic_initial_degree_le [IsDomain k]
    {w : ι → ℝ} (hwpos : ∀ i, 0 < w i) (hw : LinearIndependent ℚ w)
    {f : MvPowerSeries ι k} {γ : ι →₀ ℕ}
    (hγ : IsInitialExponent w f γ)
    (s : Finset ℕ) (p : ℕ → MvPolynomial ι k) (N : ℕ)
    (hdeg : ∀ j ∈ s, (p j).totalDegree ≤ N)
    (hnonzero : ∃ j ∈ s, p j ≠ 0)
    (hrelation : ∑ j ∈ s, (p j : MvPowerSeries ι k) * f ^ j = 0) :
    exponentDegree γ ≤ N := by
  classical
  have hwI := realWeight_injective hw
  have hf : f ≠ 0 := by intro h; simpa [h] using hγ.1
  have hp : ∀ j, p j ≠ 0 → (p j : MvPowerSeries ι k) ≠ 0 := by
    intro j hj h
    apply hj
    ext d
    simpa using congrArg (MvPowerSeries.coeff d) h
  let δ : ℕ → (ι →₀ ℕ) := fun j =>
    if h : p j ≠ 0 then (exists_initial_exponent hwpos (hp j h)).choose else 0
  have hδ : ∀ j, p j ≠ 0 → IsInitialExponent w (p j : MvPowerSeries ι k) (δ j) := by
    intro j hj
    dsimp [δ]
    simp only [dite_eq_left hj]
    exact (exists_initial_exponent hwpos (hp j hj)).choose_spec
  let F : ℕ → MvPowerSeries ι k := fun j => (p j : MvPowerSeries ι k) * f ^ j
  have hFzero : ∀ j, F j ≠ 0 ↔ p j ≠ 0 := by
    intro j
    constructor
    · intro h hj
      apply h
      simp [F, hj]
    · intro h
      exact mul_ne_zero (hp j h) (pow_ne_zero _ hf)
  have hlead : ∀ j ∈ s, F j ≠ 0 →
      IsInitialExponent w (F j) (δ j + j • γ) := by
    intro j _ hj
    exact (hδ j ((hFzero j).mp hj)).mul hwI (hγ.pow hwI j)
  have hFnz : ∃ j ∈ s, F j ≠ 0 := by
    obtain ⟨j, hj, hpj⟩ := hnonzero
    exact ⟨j, hj, (hFzero j).mpr hpj⟩
  obtain ⟨j, hj, l, hl, hjl, hFj, hFl, heq⟩ :=
    initial_tie_of_sum_eq_zero w hwI s F (fun j => δ j + j • γ)
      hlead hFnz hrelation
  have hδj := (initial_polynomial_degree_le (hδ j ((hFzero j).mp hFj))).trans (hdeg j hj)
  have hδl := (initial_polynomial_degree_le (hδ l ((hFzero l).mp hFl))).trans (hdeg l hl)
  have heq' := congrArg exponentDegree heq
  simp only [exponentDegree_add, exponentDegree_nsmul] at heq'
  rcases lt_or_gt_of_ne hjl with hlt | hgt
  · have hmult := Nat.mul_le_mul_right (exponentDegree γ) (Nat.succ_le_of_lt hlt)
    nlinarith
  · have hmult := Nat.mul_le_mul_right (exponentDegree γ) (Nat.succ_le_of_lt hgt)
    nlinarith

end AlgebraicDegree
end CartierSections
end OAI
