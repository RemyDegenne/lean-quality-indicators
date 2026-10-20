open Polynomial

open scoped Polynomial.Bivariate

noncomputable section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

lemma ω_eq_map_of_twoω_eq {n : ℤ} {q : Universal.Poly[X][Y]}
    (hq : Universal.curve.twoω n = 2 * q) :
    W.ω n = q.map (mapRingHom (Universal.specialize W)) := by
  rw [ω, hq, Universal.halve_two_mul]

end WeierstrassCurve
end
