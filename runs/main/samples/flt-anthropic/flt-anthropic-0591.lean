namespace P2MW.S_WeierstrassCurve_IsCyclicGenKernel_exists_moduleFinite_represents

set_option autoImplicit false

universe u

open Polynomial

namespace CycGenRepBody

noncomputable section

section univ

variable (B : Type u) [CommRing B] (d : ℕ)

variable {B d}

lemma coeff_hU (n : ℕ) :
    (hU B d).coeff n = if hn : n < d then MvPolynomial.X ⟨n, hn⟩ else if n = d then 1 else 0 := by
  rw [hU, coeff_add, coeff_X_pow, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hn : n < d
  · rw [dif_pos hn, if_neg hn.ne, zero_add, Finset.sum_eq_single ⟨n, hn⟩]
    · simp
    · rintro ⟨b, hb⟩ - hne
      rw [if_neg]
      intro h
      exact hne (Fin.ext h.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [dif_neg hn]
    rw [Finset.sum_eq_zero, add_zero]
    rintro ⟨b, hb⟩ -
    rw [if_neg]
    intro h
    exact hn (h ▸ hb)

end univ
end
end CycGenRepBody
end P2MW.S_WeierstrassCurve_IsCyclicGenKernel_exists_moduleFinite_represents
