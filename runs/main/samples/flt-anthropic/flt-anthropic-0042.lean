namespace P2MW.S_CerednikDrinfeld_FormalOmega_Omega_exists_scheme_equiv_nilpPoints_and_isOpenImmersion_of_isNoetherianRing

attribute [-instance] CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀

set_option autoImplicit false

open scoped PadicInt Padic TensorProduct

open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

open CategoryTheory AlgebraicGeometry

namespace RepCore

variable (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [Algebra ℤ_[p] C]

theorem Fmap_eq {A B : Type} [CommRing A] [CommRing B] [Algebra C A] [Algebra C B] (φ : A →ₐ[C] B) (s : F p C A) :
    Fmap p C A B φ s =
      (letI := compAlg p C A; letI := compAlg p C B; haveI := compTower p C A; haveI := compTower p C B
       (Omega ℚ_[p] (p : ℤ_[p])).map (φ.restrictScalars ℤ_[p]) s) := rfl

end RepCore
end P2MW.S_CerednikDrinfeld_FormalOmega_Omega_exists_scheme_equiv_nilpPoints_and_isOpenImmersion_of_isNoetherianRing
