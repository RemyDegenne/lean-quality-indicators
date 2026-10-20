@[expose] public section

noncomputable section

namespace PeriodPair

variable (L : PeriodPair)

theorem notMem_lattice_of_mem_fund {z : ℂ} (hz : z ∈ L.fundamentalParallelogram)
    (hz0 : z ≠ 0) : z ∉ L.lattice := by
  obtain ⟨s, ⟨hs0, hs1⟩, t, ⟨ht0, ht1⟩, rfl⟩ := hz
  intro hlat
  rw [mem_lattice] at hlat
  obtain ⟨m, n, hmn⟩ := hlat
  have hmn' : (s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂ = (m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂ := by
    rw [hmn]; simp [Complex.real_smul]
  have key : (s - (m : ℝ)) • L.ω₁ + (t - (n : ℝ)) • L.ω₂ = 0 := by
    simp only [sub_smul, Complex.real_smul]
    push_cast
    linear_combination hmn'
  obtain ⟨hsm, htn⟩ := LinearIndependent.pair_iff.mp L.indep (s - (m : ℝ)) (t - (n : ℝ)) key
  have hs : (m : ℝ) = s := (sub_eq_zero.mp hsm).symm
  have ht : (n : ℝ) = t := (sub_eq_zero.mp htn).symm
  have hm0 : m = 0 := by
    have h1 : (0 : ℝ) ≤ (m : ℝ) := hs ▸ hs0
    have h2 : (m : ℝ) < 1 := hs ▸ hs1
    have : (0 : ℤ) ≤ m := by exact_mod_cast h1
    have : m < 1 := by exact_mod_cast h2
    omega
  have hn0 : n = 0 := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) := ht ▸ ht0
    have h2 : (n : ℝ) < 1 := ht ▸ ht1
    have : (0 : ℤ) ≤ n := by exact_mod_cast h1
    have : n < 1 := by exact_mod_cast h2
    omega
  apply hz0
  rw [← hs, ← ht, hm0, hn0]
  simp

end PeriodPair
end
end
