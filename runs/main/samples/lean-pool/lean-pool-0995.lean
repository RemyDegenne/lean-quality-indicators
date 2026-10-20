@[expose] public section

open scoped BigOperators ContDiff

open NashEmbedding.Sobolev Matrix

noncomputable
section

namespace NashEmbedding

lemma pderiv_pderiv_freeEmb₀ (n : ℕ) (a b : Fin n) (x : Fin n → ℝ) :
    (fun k => pderiv a (pderiv b (fun y => freeEmb₀ n y k)) x) = fun k =>
      match k with
      | Sum.inl i => -(if a = i then 1 else 0) * (if b = i then 1 else 0) * Real.cos (x i)
      | Sum.inr (Sum.inl i) => -(if a = i then 1 else 0) * (if b = i then 1 else 0) * Real.sin (x i)
      | Sum.inr (Sum.inr (Sum.inl p)) =>
          -((if a = p.1.1 then 1 else 0) + (if a = p.1.2 then 1 else 0))
            * ((if b = p.1.1 then 1 else 0) + (if b = p.1.2 then 1 else 0)) * Real.cos (x p.1.1
                + x p.1.2)
      | Sum.inr (Sum.inr (Sum.inr p)) =>
          -((if a = p.1.1 then 1 else 0) + (if a = p.1.2 then 1 else 0))
            * ((if b = p.1.1 then 1 else 0) + (if b = p.1.2 then 1 else 0)) * Real.sin (x p.1.1
                + x p.1.2) := by
  funext k
  rcases k with i | i | p | p
  · have h : pderiv b (fun y : Fin n → ℝ => Real.cos (y i))
        = fun y => -(if b = i then 1 else 0) * Real.sin (y i) :=
      funext fun y => pderiv_cos_coord b i y
    change pderiv a (pderiv b (fun y : Fin n → ℝ => Real.cos (y i))) x = _
    rw [h, pderiv_const_mul _ (hasFDerivAt_sin_coord i x) a, pderiv_sin_coord]
    ring
  · have h : pderiv b (fun y : Fin n → ℝ => Real.sin (y i))
        = fun y => (if b = i then 1 else 0) * Real.cos (y i) :=
      funext fun y => pderiv_sin_coord b i y
    change pderiv a (pderiv b (fun y : Fin n → ℝ => Real.sin (y i))) x = _
    rw [h, pderiv_const_mul _ (hasFDerivAt_cos_coord i x) a, pderiv_cos_coord]
    ring
  · have h : pderiv b (fun y : Fin n → ℝ => Real.cos (y p.1.1 + y p.1.2))
        = fun y => -((if b = p.1.1 then 1 else 0) + (if b = p.1.2 then 1 else 0))
            * Real.sin (y p.1.1 + y p.1.2) :=
      funext fun y => pderiv_cos_coord_add b p.1.1 p.1.2 y
    change pderiv a (pderiv b (fun y : Fin n → ℝ => Real.cos (y p.1.1 + y p.1.2))) x = _
    rw [h, pderiv_const_mul _ (hasFDerivAt_sin_coord_add p.1.1 p.1.2 x) a, pderiv_sin_coord_add]
    ring
  · have h : pderiv b (fun y : Fin n → ℝ => Real.sin (y p.1.1 + y p.1.2))
        = fun y => ((if b = p.1.1 then 1 else 0) + (if b = p.1.2 then 1 else 0))
            * Real.cos (y p.1.1 + y p.1.2) :=
      funext fun y => pderiv_sin_coord_add b p.1.1 p.1.2 y
    change pderiv a (pderiv b (fun y : Fin n → ℝ => Real.sin (y p.1.1 + y p.1.2))) x = _
    rw [h, pderiv_const_mul _ (hasFDerivAt_cos_coord_add p.1.1 p.1.2 x) a, pderiv_cos_coord_add]
    ring

end NashEmbedding
end
end
