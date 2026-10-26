import Mathlib
import P2M.Util
namespace P2MW.S_MvPolynomial_formallySmooth_and_free_and_finite_kaehlerDifferential_of_isLocalization

set_option autoImplicit false

open MvPolynomial TensorProduct KaehlerDifferential

theorem solution
    (R : Type) [CommRing R] {n : ℕ} (M : Submonoid (MvPolynomial (Fin n) R))
    (P : Type) [CommRing P] [Algebra (MvPolynomial (Fin n) R) P] [IsLocalization M P]
    [Algebra R P] [IsScalarTower R (MvPolynomial (Fin n) R) P] :
    Algebra.FormallySmooth R P ∧ Module.Free P Ω[P⁄R] ∧ Module.Finite P Ω[P⁄R] := by
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin n) R) P := Algebra.FormallyEtale.of_isLocalization M
  haveI : Algebra.FormallySmooth (MvPolynomial (Fin n) R) P := Algebra.FormallySmooth.of_isLocalization M
  have h1 : Algebra.FormallySmooth R P := Algebra.FormallySmooth.comp R (MvPolynomial (Fin n) R) P
  let e : P ⊗[MvPolynomial (Fin n) R] Ω[MvPolynomial (Fin n) R⁄R] ≃ₗ[P] Ω[P⁄R] :=
    tensorKaehlerEquivOfFormallyEtale R (MvPolynomial (Fin n) R) P
  let b := Algebra.TensorProduct.basis P (mvPolynomialBasis R (Fin n))
  haveI : Module.Free P (P ⊗[MvPolynomial (Fin n) R] Ω[MvPolynomial (Fin n) R⁄R]) := Module.Free.of_basis b
  haveI : Module.Finite P (P ⊗[MvPolynomial (Fin n) R] Ω[MvPolynomial (Fin n) R⁄R]) := Module.Finite.of_basis b
  exact ⟨h1, Module.Free.of_equiv e, Module.Finite.equiv e⟩
