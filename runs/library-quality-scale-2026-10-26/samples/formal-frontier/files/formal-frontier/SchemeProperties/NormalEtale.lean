/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.Normal
public import SchemeProperties.LocallyNormalRing.Pi
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

@[expose] public section

set_option warningAsError true

/-!
# Étale algebras over locally normal rings

This file proves that étale algebras over locally normal rings are locally
normal. The base and target may live in independent universes, and both may
be disconnected. Étale includes finite presentation, not merely formal étaleness.

The proof reuses Mathlib's smooth integral-closure base change and decomposition
of étale algebras over a field into finite products of fields. The historical
finite-étale theorem names remain as deprecated compatibility bridges.
-/

open Polynomial
open scoped TensorProduct

universe u v

noncomputable section

private theorem smooth_isIntegrallyClosedIn_baseChange_fraction
    {R S K : Type*} [CommRing R] [CommRing S] [Field K]
    [Algebra R S] [Algebra R K] [IsFractionRing R K]
    [IsIntegrallyClosed R] [Algebra.Smooth R S] :
    IsIntegrallyClosedIn S (S ⊗[R] K) := by
  rw [isIntegrallyClosedIn_iff]
  refine ⟨Algebra.TensorProduct.includeLeft_injective (R := R) (S := S) (A := S) (B := K)
    (IsFractionRing.injective R K), ?_⟩
  intro x hx
  let eIC : integralClosure R K ≃ₐ[R] R :=
    (Subalgebra.equivOfEq _ _ (IsIntegrallyClosed.integralClosure_eq_bot R K)).trans
      (Algebra.botEquivOfInjective (IsFractionRing.injective R K))
  let e : S ⊗[R] integralClosure R K ≃ₐ[S] S :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl) eIC).trans
      (Algebra.TensorProduct.rid R S S)
  obtain ⟨y, hy⟩ :=
    TensorProduct.toIntegralClosure_bijective_of_smooth.surjective ⟨x, hx⟩
  refine ⟨e y, ?_⟩
  have hy' := congr_arg Subtype.val hy
  change ((TensorProduct.toIntegralClosure R S K y : integralClosure S (S ⊗[R] K)) :
    S ⊗[R] K) = x at hy'
  change (Algebra.TensorProduct.includeLeft : S →ₐ[S] S ⊗[R] K) (e y) = x
  rw [← hy']
  refine TensorProduct.inductionOn y (motive := fun y ↦
    (Algebra.TensorProduct.includeLeft : S →ₐ[S] S ⊗[R] K) (e y) =
      ((TensorProduct.toIntegralClosure R S K y :
        integralClosure S (S ⊗[R] K)) : S ⊗[R] K)) ?_ ?_
  · intro s z
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (by
      rw [← IsIntegrallyClosed.integralClosure_eq_bot R K]
      exact z.property)
    have hz : z = algebraMap R (integralClosure R K) r := Subtype.ext hr.symm
    subst z
    simp [e, eIC, TensorProduct.toIntegralClosure]
    simpa only [Algebra.smul_def, mul_one] using
      (TensorProduct.smul_tmul r s (1 : K))
  · intro y z hy hz
    calc
      (Algebra.TensorProduct.includeLeft : S →ₐ[S] S ⊗[R] K) (e (y + z)) =
          Algebra.TensorProduct.includeLeft (e y + e z) := by rw [map_add]
      _ = Algebra.TensorProduct.includeLeft (e y) +
          Algebra.TensorProduct.includeLeft (e z) := by rw [map_add]
      _ = ((TensorProduct.toIntegralClosure R S K y :
          integralClosure S (S ⊗[R] K)) : S ⊗[R] K) +
          ((TensorProduct.toIntegralClosure R S K z :
            integralClosure S (S ⊗[R] K)) : S ⊗[R] K) := by rw [hy, hz]
      _ = ((TensorProduct.toIntegralClosure R S K y +
          TensorProduct.toIntegralClosure R S K z :
            integralClosure S (S ⊗[R] K)) : S ⊗[R] K) := by rfl
      _ = ((TensorProduct.toIntegralClosure R S K (y + z) :
          integralClosure S (S ⊗[R] K)) : S ⊗[R] K) := by rw [map_add]

private theorem isIntegral_pi_single
    {R I : Type*} (S : I → Type*) [CommRing R] [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)] [DecidableEq I] (i : I) {x : S i}
    (hx : IsIntegral R x) : IsIntegral R (Pi.single i x : ∀ i, S i) := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p * X, hp.mul monic_X, ?_⟩
  ext j
  by_cases hji : j = i
  · subst j
    have heval :
        (eval₂ (algebraMap R (∀ j, S j)) (Pi.single i x) p) i =
          eval₂ (algebraMap R (S i)) x p := by
      calc
        _ = eval₂ ((Pi.evalRingHom S i).comp (algebraMap R (∀ j, S j)))
            ((Pi.evalRingHom S i) (Pi.single i x)) p :=
          hom_eval₂ p (algebraMap R (∀ j, S j)) (Pi.evalRingHom S i)
            (Pi.single i x)
        _ = _ := by
          rw [show (Pi.evalRingHom S i).comp (algebraMap R (∀ j, S j)) =
              algebraMap R (S i) by ext r; rfl]
          simp
    rw [eval₂_mul, eval₂_X]
    simp only [Pi.mul_apply, Pi.zero_apply, Pi.single_eq_same]
    rw [heval, hpx, zero_mul]
  · simp [hji]

private theorem eval_range_isIntegralClosure
    {R A I : Type*} (S : I → Type*) [CommRing R] [CommRing A]
    [∀ i, CommRing (S i)] [Algebra R A] [∀ i, Algebra R (S i)]
    [Algebra A (∀ i, S i)] [IsScalarTower R A (∀ i, S i)]
    [IsIntegralClosure A R (∀ i, S i)] (i : I) :
    let f : A →ₐ[R] S i :=
      (Pi.evalAlgHom R S i).comp (IsScalarTower.toAlgHom R A (∀ i, S i))
    IsIntegralClosure f.range R (S i) := by
  classical
  let f : A →ₐ[R] S i :=
    (Pi.evalAlgHom R S i).comp (IsScalarTower.toAlgHom R A (∀ i, S i))
  refine { algebraMap_injective := Subtype.val_injective, isIntegral_iff := ?_ }
  intro x
  constructor
  · intro hx
    have hsingle : IsIntegral R (Pi.single i x : ∀ i, S i) :=
      isIntegral_pi_single S i hx
    obtain ⟨a, ha⟩ :=
      (IsIntegralClosure.isIntegral_iff (A := A) (R := R) (B := ∀ i, S i)).mp hsingle
    refine ⟨⟨x, ?_⟩, rfl⟩
    exact ⟨a, by simpa [f] using congr_fun ha i⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := y.property
    change IsIntegral R (y : S i)
    rw [← ha]
    exact (IsIntegralClosure.isIntegral R (∀ i, S i) a).map f

private theorem coordinateRange_bijective
    {R A I : Type*} (S : I → Type*) [CommRing R] [CommRing A]
    [∀ i, CommRing (S i)] [Algebra R A] [∀ i, Algebra R (S i)]
    [Algebra A (∀ i, S i)] [IsScalarTower R A (∀ i, S i)]
    [IsIntegralClosure A R (∀ i, S i)] [Finite I] :
    let f : A →ₐ[R] (∀ i, S i) := IsScalarTower.toAlgHom R A (∀ i, S i)
    let fi : ∀ i, A →ₐ[R] S i := fun i ↦ (Pi.evalAlgHom R S i).comp f
    Function.Bijective (AlgHom.pi fun i ↦ (fi i).rangeRestrict) := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  let f : A →ₐ[R] (∀ i, S i) := IsScalarTower.toAlgHom R A (∀ i, S i)
  let fi : ∀ i, A →ₐ[R] S i := fun i ↦ (Pi.evalAlgHom R S i).comp f
  let g : A →ₐ[R] (∀ i, (fi i).range) := AlgHom.pi fun i ↦ (fi i).rangeRestrict
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply IsIntegralClosure.algebraMap_injective A R (∀ i, S i)
    ext i
    exact congr_arg Subtype.val (congr_fun hab i)
  · intro y
    choose a ha using fun i ↦ (y i).property
    have hy (i : I) : IsIntegral R (y i : S i) := by
      rw [← ha i]
      exact (IsIntegralClosure.isIntegral R (∀ i, S i) (a i)).map (fi i)
    have hsingle (i : I) : IsIntegral R (Pi.single i (y i : S i) : ∀ i, S i) :=
      isIntegral_pi_single S i (hy i)
    choose b hb using fun i ↦
      (IsIntegralClosure.isIntegral_iff (A := A) (R := R) (B := ∀ i, S i)).mp
        (hsingle i)
    refine ⟨∑ i, b i, ?_⟩
    ext i
    change f (∑ j, b j) i = (y i : S i)
    rw [map_sum]
    simp only [Finset.sum_apply]
    calc
      _ = ∑ j, (Pi.single j (y j : S j) : ∀ i, S i) i :=
        Finset.sum_congr rfl fun j _ ↦ congr_fun (hb j) i
      _ = _ := by simp

private theorem coordinateRange_isIntegrallyClosed
    {R A I : Type*} (S : I → Type*) [CommRing R] [CommRing A]
    [∀ i, Field (S i)] [Algebra R A] [∀ i, Algebra R (S i)]
    [Algebra A (∀ i, S i)] [IsScalarTower R A (∀ i, S i)]
    [IsIntegralClosure A R (∀ i, S i)] (i : I) :
    let f : A →ₐ[R] S i :=
      (Pi.evalAlgHom R S i).comp (IsScalarTower.toAlgHom R A (∀ i, S i))
    IsIntegrallyClosed f.range := by
  let f : A →ₐ[R] S i :=
    (Pi.evalAlgHom R S i).comp (IsScalarTower.toAlgHom R A (∀ i, S i))
  let _ : IsIntegralClosure f.range R (S i) := eval_range_isIntegralClosure S i
  let _ : IsIntegrallyClosedIn f.range (S i) :=
    IsIntegrallyClosedIn.of_isIntegralClosure R
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn f.range (S i)

private theorem integralClosure_pi_fields_isLocallyNormal
    {R A I : Type*} (S : I → Type*) [CommRing R] [CommRing A]
    [∀ i, Field (S i)] [Algebra R A] [∀ i, Algebra R (S i)]
    [Algebra A (∀ i, S i)] [IsScalarTower R A (∀ i, S i)]
    [IsIntegralClosure A R (∀ i, S i)] [Finite I] : IsLocallyNormalRing A := by
  let f : A →ₐ[R] (∀ i, S i) := IsScalarTower.toAlgHom R A (∀ i, S i)
  let fi : ∀ i, A →ₐ[R] S i := fun i ↦ (Pi.evalAlgHom R S i).comp f
  let g : A →ₐ[R] (∀ i, (fi i).range) := AlgHom.pi fun i ↦ (fi i).rangeRestrict
  let e : A ≃ₐ[R] (∀ i, (fi i).range) :=
    AlgEquiv.ofBijective g (coordinateRange_bijective S)
  let _ (i : I) : IsIntegrallyClosed (fi i).range :=
    coordinateRange_isIntegrallyClosed S i
  let _ (i : I) : IsLocallyNormalRing (fi i).range :=
    isLocallyNormalRing_of_isDomain (fi i).range
  let _ : IsLocallyNormalRing (∀ i, (fi i).range) := IsLocallyNormalRing.pi _
  exact IsLocallyNormalRing.of_ringEquiv e.symm.toRingEquiv

/-- An étale algebra over an integrally closed domain is locally normal.
The algebra itself may be disconnected. -/
theorem IsLocallyNormalRing.of_etale_of_isDomain
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsIntegrallyClosed R] [Algebra.Etale R S] :
    IsLocallyNormalRing S := by
  let K := FractionRing R
  let P := S ⊗[R] K
  -- Keep the left S-action separate from the right K-action of the generic fibre.
  let leftAlgebra : Algebra S P := inferInstance
  let rightAlgebra : Algebra K P := Algebra.TensorProduct.rightAlgebra
  have hclosed : @IsIntegrallyClosedIn S P _ _ leftAlgebra :=
    smooth_isIntegrallyClosedIn_baseChange_fraction
  let _ : Algebra K P := rightAlgebra
  let ecomm : (K ⊗[R] S) ≃ₐ[K] P :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R K S).toRingEquiv) <| by
      intro k
      change (Algebra.TensorProduct.comm R K S) (k ⊗ₜ[R] (1 : S)) =
        (1 : S) ⊗ₜ[R] k
      rfl
  let _ : Algebra.Etale K P := Algebra.Etale.of_equiv ecomm
  have hEtale : Algebra.Etale K P := inferInstance
  obtain ⟨I, hI, L, hLfield, hLalg, e, _⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := P)).mp hEtale
  let _ : Finite I := hI
  let _ (i : I) : Field (L i) := hLfield i
  let _ (i : I) : Algebra K (L i) := hLalg i
  -- Each coordinate receives its S-action from S → P → Π i, L i.
  let _ (i : I) : Algebra S (L i) :=
    ((Pi.evalRingHom L i).comp
      (e.toRingEquiv.toRingHom.comp (@algebraMap S P _ _ leftAlgebra))).toAlgebra
  let _ : Algebra S P := leftAlgebra
  let E : P ≃ₐ[S] (∀ i, L i) :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) <| by
      intro s
      ext i
      rfl
  -- Closedness already means integral closure over S itself: no integrality of S/R.
  let _ : IsIntegralClosure S S (∀ i, L i) := E.isIntegrallyClosedIn.mp hclosed
  exact integralClosure_pi_fields_isLocallyNormal (R := S) (A := S) (I := I) L

/-- An étale algebra over a locally normal ring is locally normal. -/
theorem IsLocallyNormalRing.of_etale
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocallyNormalRing R] [Algebra.Etale R S] :
    IsLocallyNormalRing S := by
  constructor <;> intro q
  all_goals
    let p : Ideal R := q.asIdeal.under R
    let Rₚ := Localization.AtPrime p
    let B := Rₚ ⊗[R] S
    let A := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
    let Q : Ideal A := q.asIdeal.map (algebraMap S A)
    let _ : p.IsPrime := (inferInstance : q.asIdeal.IsPrime).under R
    let _ : IsDomain Rₚ := IsLocallyNormalRing.isDomain_atPrime ⟨p, inferInstance⟩
    let _ : IsIntegrallyClosed Rₚ :=
      IsLocallyNormalRing.isIntegrallyClosed_atPrime ⟨p, inferInstance⟩
    let _ : Algebra.Etale Rₚ B := inferInstance
    let _ : IsLocallyNormalRing B :=
      IsLocallyNormalRing.of_etale_of_isDomain (R := Rₚ) (S := B)
    let e : B ≃ₐ[Rₚ] A := Localization.tensorRightAlgEquiv p.primeCompl S
    let _ : IsLocallyNormalRing A := IsLocallyNormalRing.of_ringEquiv e.toRingEquiv
    have hdisj :
        Disjoint ((Algebra.algebraMapSubmonoid S p.primeCompl : Submonoid S) : Set S)
          (q.asIdeal : Set S) :=
      Ideal.disjoint_primeCompl_of_liesOver q.asIdeal p
    let _ : Q.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint
        (Algebra.algebraMapSubmonoid S p.primeCompl) A q.asIdeal inferInstance hdisj
    have hQunder : Q.under S = q.asIdeal :=
      IsLocalization.under_map_of_isPrime_disjoint
        (Algebra.algebraMapSubmonoid S p.primeCompl) A inferInstance hdisj
    let _ : Algebra S (Localization.AtPrime Q) :=
      ((algebraMap A (Localization.AtPrime Q)).comp (algebraMap S A)).toAlgebra
    let _ : SMul S A := Algebra.toSMul
    let _ : SMul A (Localization.AtPrime Q) := Algebra.toSMul
    let _ : SMul S (Localization.AtPrime Q) := Algebra.toSMul
    let hTower : IsScalarTower S A (Localization.AtPrime Q) :=
      IsScalarTower.of_algebraMap_eq' rfl
    have hlocUnder :
        IsLocalization (Q.under S).primeCompl (Localization.AtPrime Q) :=
      @IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        S _ (Algebra.algebraMapSubmonoid S p.primeCompl) A _ _
        (Localization.AtPrime Q) _ _ _ hTower _ Q inferInstance _
    have hloc : IsLocalization q.asIdeal.primeCompl (Localization.AtPrime Q) := by
      simpa only [hQunder] using hlocUnder
    let _ : IsLocalization q.asIdeal.primeCompl (Localization.AtPrime Q) := hloc
    let eQ : Localization.AtPrime q.asIdeal ≃+* Localization.AtPrime Q :=
      (IsLocalization.algEquiv q.asIdeal.primeCompl
        (Localization.AtPrime q.asIdeal) (Localization.AtPrime Q)).toRingEquiv
  · let _ : IsDomain (Localization.AtPrime Q) :=
      IsLocallyNormalRing.isDomain_atPrime ⟨Q, inferInstance⟩
    exact eQ.toMulEquiv.isDomain _
  · let _ : IsIntegrallyClosed (Localization.AtPrime Q) :=
      IsLocallyNormalRing.isIntegrallyClosed_atPrime ⟨Q, inferInstance⟩
    exact IsIntegrallyClosed.of_equiv eQ.symm

/-- Historical finite-étale interface for local normality over an integrally closed domain.
The finiteness parameter is retained solely for compatibility. -/
@[deprecated IsLocallyNormalRing.of_etale_of_isDomain (since := "2026-10-17")]
theorem IsLocallyNormalRing.of_finiteEtale_of_isDomain
    {R : Type*} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsIntegrallyClosed R] [Algebra.Etale R S] [Module.Finite R S] :
    IsLocallyNormalRing S :=
  IsLocallyNormalRing.of_etale_of_isDomain (R := R) (S := S)

/-- Historical finite-étale interface for local normality.
The finiteness parameter is retained solely for compatibility. -/
@[deprecated IsLocallyNormalRing.of_etale (since := "2026-10-17")]
theorem IsLocallyNormalRing.of_finiteEtale
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocallyNormalRing R] [Algebra.Etale R S] [Module.Finite R S] :
    IsLocallyNormalRing S :=
  IsLocallyNormalRing.of_etale (R := R) (S := S)
