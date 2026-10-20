@[expose] public section

local notation3 "x" => (0 : Fin 3)

local notation3 "y" => (1 : Fin 3)

local notation3 "z" => (2 : Fin 3)

open MvPolynomial

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow])

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_C, map_X, map_neg, map_add, map_sub, map_mul, map_pow,
    map_div₀, WeierstrassCurve.map, Function.comp_apply])

local macro "matrix_simp" : tactic =>
  `(tactic| simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.smul_empty, Matrix.smul_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two])

local macro "pderiv_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, pderiv_mul, pderiv_pow,
    pderiv_C, pderiv_X_self, pderiv_X_of_ne one_ne_zero, pderiv_X_of_ne one_ne_zero.symm,
    pderiv_X_of_ne (by decide : z ≠ x), pderiv_X_of_ne (by decide : x ≠ z),
    pderiv_X_of_ne (by decide : z ≠ y), pderiv_X_of_ne (by decide : y ≠ z)])

universe r s u v

variable {R : Type r} {F : Type u}

namespace WeierstrassCurve

namespace Jacobian

variable [CommRing R] [Field F] {W' : Jacobian R} {W : Jacobian F} {S : Type s} [CommRing S]
  {A : Type u} [CommRing A] {B : Type v} [CommRing B] {K : Type v} [Field K]

scoped instance : SMul R <| Fin 3 → R :=
  ⟨fun u P => ![u ^ 2 * P x, u ^ 3 * P y, u * P z]⟩

scoped instance : MulAction R <| Fin 3 → R where
  one_smul _ := by simp only [smul_fin3, one_pow, one_mul, fin3_def]
  mul_smul _ _ _ := by simp only [smul_fin3, mul_pow, mul_assoc, fin3_def_ext]

@[reducible]
scoped instance : Setoid <| Fin 3 → R :=
  MulAction.orbitRel Rˣ <| Fin 3 → R

lemma comp_equiv_comp (f : F →+* K) {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) : f ∘ P ≈ f ∘ Q ↔ P ≈ Q := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases hz : f (P z) = 0
    · exact equiv_of_Z_eq_zero hP hQ ((map_eq_zero_iff f f.injective).mp hz) <|
        (map_eq_zero_iff f f.injective).mp <| (Z_eq_zero_of_equiv h).mp hz
    · refine equiv_of_X_eq_of_Y_eq ((map_ne_zero_iff f f.injective).mp hz)
        ((map_ne_zero_iff f f.injective).mp <| hz.comp (Z_eq_zero_of_equiv h).mpr) ?_ ?_
      all_goals apply f.injective; map_simp
      exacts [X_eq_of_equiv h, Y_eq_of_equiv h]
  · rcases h with ⟨u, rfl⟩
    exact ⟨Units.map f u, (comp_smul ..).symm⟩

end Jacobian
end WeierstrassCurve
end
