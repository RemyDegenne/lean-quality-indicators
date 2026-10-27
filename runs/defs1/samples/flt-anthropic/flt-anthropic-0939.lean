namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuliT_finite_etale_of_forall_local

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField

p2m_open

namespace CerednikDrinfeld

namespace QM

namespace FakeEllipticCurve

p2m_open

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N₀ : ℕ}

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField

p2m_open

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField

p2m_open

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField

p2m_open

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField

p2m_open

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField

p2m_open

namespace CerednikDrinfeld p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve.ExtraLevel QM.FakeEllipticCurve QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_openCover QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia" namespace QM p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.WithFullLevel FakeEllipticCurve.WithFullLevel.Iso FakeEllipticCurve.WithFullLevel.IsPullback IsFineModuli FakeEllipticCurve.ExtraLevel FakeEllipticCurve.WithExtraLevel mapPt mapPt_coe FactorsThrough FakeEllipticCurve FakeEllipticCurve.IsPullbackVia FakeEllipticCurve.WithFullLevel.exists_isPullback FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_openCover FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia FakeEllipticCurve.WithFullLevel.IsoTVia IsFineModuliT" namespace ZUniq end CerednikDrinfeld.QM.ZUniq

p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.QM" in

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

set_option linter.unusedTactic false

open scoped TensorProduct Quaternion NumberField

p2m_open

namespace BodyL2

universe u

variable {a b : ℚ} {N₀ : ℕ}

def RepresentsExtraLevel (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ) {S : Type} [CommRing S]
    (u : FakeEllipticCurve.WithFullLevel Λ N₀ m S) {Z : Scheme.{0}} (ζ : Z ⟶ Spec (CommRingCat.of S))
    (ptZ : ∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ N₀ m T),
      FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → u'.1.ExtraLevel N → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ) :
    Prop :=
  (∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ N₀ m T)
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u') (K K' : u'.1.ExtraLevel N),
            (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of T)) (P : SchemeHomOver t u'.1.f),
              FactorsThrough K.levK P ↔ FactorsThrough K'.levK P) → ptZ T φ u' hu' K = ptZ T φ u' hu' K') ∧

        (∀ (T T' : Type) [CommRing T] [CommRing T'] (φ : S →+* T) (ψ : T →+* T')
            (u' : FakeEllipticCurve.WithFullLevel Λ N₀ m T) (u'' : FakeEllipticCurve.WithFullLevel Λ N₀ m T')
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u')
            (hu'' : FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ) u u'')
            (K' : u'.1.ExtraLevel N) (K'' : u''.1.ExtraLevel N) (g : u''.1.A ⟶ u'.1.A),

            FakeEllipticCurve.IsPullbackVia ψ u'.1 u''.1 g →
            (u''.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom ψ) ≫ (u'.2.P).1 →
            (∀ {T₀ : Scheme.{0}} (t : T₀ ⟶ Spec (CommRingCat.of T')) (P : SchemeHomOver t u''.1.f),
              FactorsThrough K''.levK P → ∃ P₀ : T₀ ⟶ K'.K, P₀ ≫ K'.levK = P.1 ≫ g) →
              (ptZ T' (ψ.comp φ) u'' hu'' K'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptZ T φ u' hu' K').1) ∧

        (∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ N₀ m T)
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u')
            (z : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ), ∃ K : u'.1.ExtraLevel N, ptZ T φ u' hu' K = z) ∧
        (∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ N₀ m T)
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u')
            (K K' : u'.1.ExtraLevel N), ptZ T φ u' hu' K = ptZ T φ u' hu' K' →
            ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of T)) (P : SchemeHomOver t u'.1.f),
              FactorsThrough K.levK P ↔ FactorsThrough K'.levK P)

end BodyL2
end CerednikDrinfeld
end FakeEllipticCurve
end QM
end CerednikDrinfeld
end P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuliT_finite_etale_of_forall_local
