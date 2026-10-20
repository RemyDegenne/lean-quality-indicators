@[expose] public section

open scoped WithZero

universe u v w z

namespace MvPolynomial

variable {σ : Type u} {τ : Type v}

variable {k : Type w} {l : Type z} [Field k] [Field l]

theorem weightOneValuation_map (g : k →+* l) (e : σ ↪ τ)
    (S : Set σ) (T : Set τ) (h : ∀ j : σ, e j ∈ T ↔ j ∈ S)
    (i : S) (t : T) (x : FractionRing (MvPolynomial σ k)) :
    weightOneValuation (k := l) T t (weightOneFractionMap g e x) =
      weightOneValuation (k := k) S i x := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial σ k) x
  have hq' : q ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hq
  have hweights : e ⁻¹' T = S := Set.ext fun j => h j
  by_cases hp : p = 0
  · subst p
    simp
  · have hpmap : weightOnePolynomialMap g e p ≠ 0 := by
      simpa only [map_zero] using (weightOnePolynomialMap_injective g g.injective e).ne hp
    have hqmap : weightOnePolynomialMap g e q ≠ 0 := by
      simpa only [map_zero] using (weightOnePolynomialMap_injective g g.injective e).ne hq'
    have hnat (r : MvPolynomial σ k) :
        weightOneNatOrder T (weightOnePolynomialMap g e r) = weightOneNatOrder S r := by
      rw [weightOneNatOrder_map g g.injective e T r, hweights]
    rw [map_div₀, weightOneFractionMap_polynomial, weightOneFractionMap_polynomial,
      weightOneValuation_div T t hpmap hqmap,
      weightOneValuation_div S i hp hq', hnat p, hnat q]

end MvPolynomial
end
