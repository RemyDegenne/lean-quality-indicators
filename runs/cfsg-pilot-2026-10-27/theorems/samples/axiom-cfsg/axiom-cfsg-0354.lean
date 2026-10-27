public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Kst

open Equiv

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace SixData

variable {G : Subgroup (Perm Ω)} {ω₀ : Ω} {a b : Perm Ω}

theorem eq_one_of_fix_three (h : SixData G ω₀ a b) {g : Perm Ω} (hg : g ∈ G) (hg0 : g ω₀ = ω₀)
    {x y : Ω} (hx : x ≠ ω₀) (hy : y ≠ ω₀) (hxy : x ≠ y) (hgx : g x = x) (hgy : g y = y) :
    g = 1 := by
  obtain ⟨ω₁, hω₁, hb⟩ := h.exists_fix_b
  obtain ⟨i, -, hix⟩ := h.exists_a_pow hx hω₁
  set d : Perm Ω := a ^ i with hd
  have hdG : d ∈ G := pow_mem h.a_mem i
  have hd0 : d ω₀ = ω₀ := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h.a_fix i
  have hg₂G : d * g * d⁻¹ ∈ G := mul_mem (mul_mem hdG hg) (inv_mem hdG)
  have hconj : ∀ z : Ω, g z = z → (d * g * d⁻¹) (d z) = d z := by
    intro z hz
    simp [Perm.mul_apply, hz]
  have h20 : (d * g * d⁻¹) ω₀ = ω₀ := by
    have := hconj ω₀ hg0
    rwa [hd0] at this
  have h21 : (d * g * d⁻¹) ω₁ = ω₁ := by
    have := hconj x hgx
    rwa [hix] at this
  obtain ⟨j, hj, hgj⟩ := h.eq_pow_b_of_fix_two hω₁ hb hg₂G h20 h21
  by_cases hj0 : j = 0
  · rw [hj0, pow_zero] at hgj
    have : g = d⁻¹ * (d * g * d⁻¹) * d := by group
    rw [this, hgj]
    group
  · exfalso
    have hyfix := hconj y hgy
    rw [hgj] at hyfix
    have hdy0 : d y ≠ ω₀ := by
      intro h0
      apply hy
      have := (d).injective (h0.trans hd0.symm)
      exact this
    have hdy1 : d y ≠ ω₁ := by
      intro h1
      apply hxy
      have : d x = d y := hix.trans h1.symm
      exact (d.injective this)
    rcases h.fix_b_pow hω₁ hb hj hj0 hyfix with h0 | h1
    · exact hdy0 h0
    · exact hdy1 h1

end SixData
end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Kst
end
