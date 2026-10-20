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

namespace Projective

variable [CommRing R] [Field F] {W' : Projective R} {W : Projective F} {S : Type s} [CommRing S]
  {A : Type u} [CommRing A] {B : Type v} [CommRing B] {K : Type v} [Field K]

@[reducible]
scoped instance : Setoid <| Fin 3 → R :=
  MulAction.orbitRel Rˣ <| Fin 3 → R

variable (W') (f : R →+* S)

scoped notation:max W:max "⁄" S:max => baseChange W S

variable {f} in
@[simp]
lemma map_equation (hf : Function.Injective f) (P : Fin 3 → R) :
    (W'.map f).Equation (f ∘ P) ↔ W'.Equation P := by
  simp only [Equation, map_polynomial, eval_map, ← eval₂_comp, map_eq_zero_iff f hf]

end Projective
end WeierstrassCurve
end
