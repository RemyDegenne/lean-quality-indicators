namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper

attribute [-instance] DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

universe u

noncomputable section

p2m_open

namespace AlgebraicGeometry

namespace OModulePresheaf

namespace C2Head

p2m_open

section U

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [IsProper q]
  {V' : Scheme.{u}} (p : V' ⟶ P) [IsProper p] (K' : V'.OrderedAffineCover)
  (F' : ℕ → OModulePresheaf (p ≫ q)) (φ' : ∀ k, AffHom (F' (k + 1)) (F' k))
  (G' : OModulePresheaf (p ≫ q))
  (ψ' : ∀ k, AffHom G' (F' k))
  (hψ'k : ∀ (k : ℕ) (V : V'.affineOpens),
    LinearMap.ker ((ψ' k).app V) = I ^ (k + 1) • (⊤ : Submodule A (G'.obj V.1)))
  (F : ℕ → OModulePresheaf q) (φ : ∀ k, AffHom (F (k + 1)) (F k))
  (v : ∀ k, AffHom (F k) (cechPushforward p q K' (F' k)))

  (hPC : ∀ (k : ℕ) (U : P.affineOpens),
    ((φ' k).cechPushforward p q K').app U ∘ₗ ((ψ' (k + 1)).cechPushforward p q K').app U
      = ((ψ' k).cechPushforward p q K').app U)
  (hvc : ∀ (k : ℕ) (U : P.affineOpens),
    ((φ' k).cechPushforward p q K').app U ∘ₗ (v (k + 1)).app U = (v k).app U ∘ₗ (φ k).app U)

  (hT1 : ∀ (U : P.affineOpens) (k : ℕ) (y : (F k).obj U.1),
    ∃ s : ∀ n, (F n).obj U.1, (∀ n, (φ n).app U (s (n + 1)) = s n) ∧ s k = y)

  (hT2 : ∀ (U : P.affineOpens) (k : ℕ) (s s' : ∀ n, (F n).obj U.1),
    (∀ n, (φ n).app U (s (n + 1)) = s n) → (∀ n, (φ n).app U (s' (n + 1)) = s' n) → s k = s' k →
      ∀ n, k ≤ n → s n - s' n ∈ I ^ (k + 1) • (⊤ : Submodule A ((F n).obj U.1)))

  (hA2 : ∀ (U : P.affineOpens) (L : ℕ) (s : ∀ n, (F n).obj U.1), (∀ n, (φ n).app U (s (n + 1)) = s n) →
    ∃ a : (cechPushforward p q K' G').obj U.1, ((ψ' L).cechPushforward p q K').app U a = (v L).app U (s L))

section Defu

variable (hG'c : G'.IsCoherent) (hG'q : G'.IsQuasicoherent)

theorem thr_thread (U : P.affineOpens) (k : ℕ) (y : (F k).obj U.1) (n : ℕ) :
    (φ n).app U (thr F φ hT1 U k y (n + 1)) = thr F φ hT1 U k y n := (hT1 U k y).choose_spec.1 n

end Defu
end U
end C2Head
end OModulePresheaf
end AlgebraicGeometry
end
end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper
