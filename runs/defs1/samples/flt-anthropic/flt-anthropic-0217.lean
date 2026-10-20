namespace P2MW.S_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_pow_span_X_le

set_option autoImplicit false

universe u v w t

open TensorProduct

namespace TruncBCEngine

open MvPowerSeries

section Main

variable {σ : Type w} [Finite σ] {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]

variable {ι : Type*}

scoped instance instIsScalarTowerTensorQuot (N : ℕ) :
    IsScalarTower R S (S ⊗[R] (MvPolynomial σ R ⧸ MvPolynomial.idealOfVars σ R ^ N)) :=
  TensorProduct.isScalarTower_left

noncomputable def xfam (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (σ : Type w) (N : ℕ) : σ → S ⊗[R] (MvPolynomial σ R ⧸ MvPolynomial.idealOfVars σ R ^ N) :=
  fun i => (1 : S) ⊗ₜ[R] Ideal.Quotient.mk _ (MvPolynomial.X i)

end Main
end TruncBCEngine
end P2MW.S_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_pow_span_X_le
