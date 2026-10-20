@[expose] public section

namespace BGS.Markoff

noncomputable section

variable (p : ℕ) [Fact p.Prime]

local notation "F" => ZMod

local notation "E" => quadraticFiniteField

noncomputable local instance : Fintype (E p) := Fintype.ofFinite (E p)

noncomputable local instance : DecidableEq (quadraticNormOneTorus p) := Classical.decEq _

theorem algebraMap_eval_quadraticCayleyNormPolynomial (z : F p) :
    algebraMap (F p) (E p) ((quadraticCayleyNormPolynomial p).eval z) =
      (algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p) *
        (algebraMap (F p) (E p) z - quadraticNonbaseElement p) := by
  calc
    algebraMap (F p) (E p) ((quadraticCayleyNormPolynomial p).eval z) =
        ((quadraticCayleyNormPolynomial p).map
          (algebraMap (F p) (E p))).eval (algebraMap (F p) (E p) z) := by
      rw [← Polynomial.eval₂_eq_eval_map]
      exact (Polynomial.eval₂_at_apply (algebraMap (F p) (E p)) z).symm
    _ = _ := by rw [quadraticCayleyNormPolynomial_map]; simp

end
end BGS.Markoff
end
