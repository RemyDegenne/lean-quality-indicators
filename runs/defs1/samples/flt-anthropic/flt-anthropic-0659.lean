namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_scheme_represents_subgroup_ideal_and_isClosedImmersion_toProjSpace

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

open CategoryTheory AlgebraicGeometry

open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace KernelHilb

variable (p : ℕ) [Fact p.Prime] {B₀ : Type} [CommRing B₀] (Φ : FormalODModule p B₀) (N h : ℕ)

section Dict

variable {L : Type} [CommRing L] [HopfAlgebra B₀ L] [Module.Finite B₀ L]

variable (ρ : Zp2 p → (L →ₐc[B₀] L)) (ϖ : L →ₐc[B₀] L)

variable (θ : ∀ (S : Type) [CommRing S] [Algebra B₀ S], MvPowerSeries (Fin 2) S →ₐ[S] S ⊗[B₀] L)

variable (S : Type) [CommRing S] [Algebra B₀ S]

noncomputable def toN (hθ : ThetaSpec p Φ N ρ ϖ θ) (I : Ideal (MvPowerSeries (Fin 2) S)) (hI : PZ p Φ N h S I) :
    Module.Grassmannian S (S ⊗[B₀] L) (p ^ h) :=
  letI : Module.Finite S (MvPowerSeries (Fin 2) S ⧸ I) := hI.1
  letI : Module.Projective S (MvPowerSeries (Fin 2) S ⧸ I) := hI.2.1
  let e := (exists_quotEquiv θ S (hθ.surj S) I (ker_le_of_PZ' p Φ N h ρ ϖ θ hθ S I hI)).choose
  { toSubmodule := imS θ S I
    finite_quotient := Module.Finite.equiv e
    projective_quotient := Module.Projective.of_equiv e
    rankAtStalk_eq := fun 𝔭 => by
      rw [← Module.rankAtStalk_eq_of_equiv e]
      exact rankAtStalk_of_PZ p Φ N h ρ ϖ θ S hθ I hI 𝔭 }

end Dict
end KernelHilb
end P2MW.S_CerednikDrinfeld_FormalODModule_exists_scheme_represents_subgroup_ideal_and_isClosedImmersion_toProjSpace
