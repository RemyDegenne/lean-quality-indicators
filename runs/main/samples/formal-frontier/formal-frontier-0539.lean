@[expose] public section

open scoped WithZero

universe u v w z

namespace MvPolynomial

variable {σ : Type u} {τ : Type v}

variable {k : Type w} {l : Type z} [Field k] [Field l]

local notation3 "ratio[" F "," U "," pivot "](" j ")" =>
  (algebraMap (MvPolynomial (WeightOneCoefficientVariables U pivot) F)
    (WeightOneCoefficientField F U pivot) (X (Sum.inr j)))

local notation3 "unweighted[" F "," U "," pivot "](" j ")" =>
  (algebraMap (MvPolynomial (WeightOneCoefficientVariables U pivot) F)
    (WeightOneCoefficientField F U pivot) (X (Sum.inl j)))

theorem weightOneValuation_map_of_disjoint (g : k →+* l) (e : σ ↪ τ)
    (T : Set τ) (h : ∀ j : σ, e j ∉ T) (t : T)
    {x : FractionRing (MvPolynomial σ k)} (hx : x ≠ 0) :
    weightOneValuation (k := l) T t (weightOneFractionMap g e x) = 1 := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial σ k) x
  have hq' : q ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hq
  have hp : p ≠ 0 := by
    intro hzero
    subst p
    simp at hx
  have hpmap : weightOnePolynomialMap g e p ≠ 0 := by
    simpa only [map_zero] using (weightOnePolynomialMap_injective g g.injective e).ne hp
  have hqmap : weightOnePolynomialMap g e q ≠ 0 := by
    simpa only [map_zero] using (weightOnePolynomialMap_injective g g.injective e).ne hq'
  have horder (r : MvPolynomial σ k) (hr : r ≠ 0) :
      weightOneNatOrder T (weightOnePolynomialMap g e r) = 0 := by
    have heq := weightOneOrder_map_eq_zero g g.injective e T h hr
    exact congrArg ENat.toNat heq
  rw [weightOneFractionMap_div, weightOneValuation_div T t hpmap hqmap,
    horder p hp, horder q hq']
  simp

end MvPolynomial
end
