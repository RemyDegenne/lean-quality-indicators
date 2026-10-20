@[expose] public section

local notation3 "x" => (0 : Fin 3)

local notation3 "y" => (1 : Fin 3)

local notation3 "z" => (2 : Fin 3)

open MvPolynomial

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_C, map_X, map_neg, map_add, map_sub, map_mul, map_pow,
    map_div₀, WeierstrassCurve.map, Function.comp_apply])

universe r s u v

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] [Field F] [Field K] {W' : Projective R} {W : Projective F}

namespace Projective

lemma dblXYZ_smul (P : Fin 3 → R) (u : R) : W'.dblXYZ (u • P) = u ^ 4 • W'.dblXYZ P := by
  rw [dblXYZ, dblX_smul, dblY_smul, dblZ_smul, smul_fin3, dblXYZ_X, dblXYZ_Y, dblXYZ_Z]

end Projective
end WeierstrassCurve
end
