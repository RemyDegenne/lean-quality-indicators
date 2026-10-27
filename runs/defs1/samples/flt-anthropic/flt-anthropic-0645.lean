namespace P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_stratumPoint_of_forall_representsOn_of_isPullback

set_option autoImplicit false

set_option linter.unusedVariables false

open scoped TensorProduct Quaternion NumberField

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

noncomputable section

namespace RelRepS14

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

section Frame

def uq (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (n : ℕ) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄)
    (Xbar : ℕ → Scheme.{0})
    (qbar : ∀ d : ℕ, Xbar d ⟶ pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π})))))
    (κ : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
      FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt → (X ⟶ Xbar d))
    (hB1 : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA)
      (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ)
      (hX : FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt),
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.fst fM _ = ξ ≫ (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1 ∧
      κ d S u A gA hgA X ξ pt hX ≫ qbar d ≫ pullback.snd fM _ =
        ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S)))
    (hloc : ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S]
      [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A)
      (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ), FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt)
    (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) : FakeEllipticCurve.WithFullLevel Λ N n (T ⧸ Ideal.span {algebraMap 𝒪 T π}) :=
  (CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 T π})) u).choose

end Frame
end RelRepS14
end
end P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_stratumPoint_of_forall_representsOn_of_isPullback
