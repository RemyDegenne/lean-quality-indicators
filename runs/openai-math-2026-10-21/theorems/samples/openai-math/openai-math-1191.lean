namespace OAI

namespace TwoPointCorrelations

open Finset Polynomial Matrix

theorem halasz_vinogradov_jacobian_nonsingular {p k : ℕ} [Fact p.Prime]
    (hkp : k<p) (P : Fin k → (ZMod p)[X]) (x : Fin k → ZMod p)
    (hdeg : ∀ j, (P j).natDegree ≤ j.val+1)
    (hcoeff : ∀ j, (P j).coeff (j.val+1)≠0) (hx : Function.Injective x) :
    (Matrix.of (fun i j => (P j).derivative.eval (x i))).det ≠ 0 := by
  rw [halasz_vinogradov_polynomial_jacobian P x hdeg]
  apply mul_ne_zero
  · apply prod_ne_zero_iff.mpr
    intro j _
    apply mul_ne_zero (hcoeff j)
    have hj : j.val+1<p := by omega
    have hn : ((j.val+1:ℕ):ZMod p)≠0 :=
      (ZMod.natCast_eq_zero_iff _ _).not.mpr
        (Nat.not_dvd_of_pos_of_lt (by omega : 0<j.val+1) hj)
    simpa only [Nat.cast_add,Nat.cast_one] using hn
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr hx

end TwoPointCorrelations
end OAI
