public section

open Polynomial

namespace TauCeti

variable {n : ℕ} {S : Set (Fin n → ℝ)}

theorem nonempty_delineation_integerFamily_of_signInvariant_integerProjection
    {P : Finset (MvPolynomial (Fin (n + 1)) ℤ)} (hS : IsPreconnected S)
    (h : ∀ q ∈ P.integerProjection,
      SignInvariant (fun x ↦ MvPolynomial.eval₂ (Int.castRingHom ℝ) x q) S) :
    Nonempty (Delineation fun (p : P.integerFamily) (x : S) ↦
      p.1.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) x.1)) := by
  classical
  exact nonempty_delineation_image_finSuccEquiv_map_of_signInvariant_collinsProjection
    (RingHom.injective_int _) hS h

end TauCeti
end
