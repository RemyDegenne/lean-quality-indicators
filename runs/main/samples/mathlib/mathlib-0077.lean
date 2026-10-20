variable {K : Type*} [Field K]

open IntermediateField

namespace RatFunc.Luroth

noncomputable section

open algebraAdjoinAdjoin Polynomial

open scoped Polynomial.Bivariate

variable {E : IntermediateField K K⟮X⟯}

lemma Φ_natDegree_eq_φ_natDegree (h : E ≠ ⊥) : (Φ E).natDegree = (φ E).natDegree := by
  rw [← natDegree_map_eq_of_injective (algebraMap_injective K), ← C_c_mul_φ h,
    natDegree_mul (C_ne_zero.mpr (c_ne_zero h)) (map_ne_zero (φ_ne_zero h)), natDegree_C,
    natDegree_map, zero_add]

end
end RatFunc.Luroth
