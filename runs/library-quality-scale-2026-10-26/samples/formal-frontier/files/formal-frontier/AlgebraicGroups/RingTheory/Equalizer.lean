/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Equalizers of algebra homomorphisms

This file records functoriality, idempotent-localization, and integrality
criteria for the equalizer of two algebra homomorphisms. In particular, a
commuting morphism of pairs whose ambient maps are idempotent localizations
induces an idempotent localization on equalizers. Finitely many monic equations
supported on a complete family of idempotents also patch to a single monic
equation over the equalizer.

Unlike flat base change of equalizers, localization here uses the elementary
equality criterion for an idempotent localization. Patching needs idempotence
and a sum of one, not pairwise orthogonality. With an empty index type, the
completeness hypothesis implies `0 = 1`.

## References

* Stacks Project, Lemmas 39.23.3 and 39.23.4 (tags 03BI and 03BJ), for
  invariant rank pieces and the norm-based integrality argument. The monic
  equations on each piece are inputs to the patching theorem here.
* Mathlib, `Mathlib.Algebra.Algebra.Subalgebra.Basic` for `AlgHom.equalizer`;
  `Mathlib.RingTheory.Flat.Equalizer` for the separate flat base-change API
  `AlgHom.tensorEqualizerEquiv`; `Mathlib.RingTheory.Localization.Away.Basic`
  for idempotent localization; `Mathlib.Algebra.Polynomial.Lifts` for monic lifting.
-/

public section

open scoped Polynomial

noncomputable section

namespace IsLocalization.Away

universe uR uS

/-- Equality in a localization away from an idempotent is equality after
multiplication by that idempotent. -/
lemma algebraMap_eq_iff_mul_eq_of_isIdempotentElem
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    [Algebra R S] (e : R) (he : IsIdempotentElem e)
    [IsLocalization.Away e S] (x y : R) :
    algebraMap R S x = algebraMap R S y ↔ e * x = e * y := by
  rw [IsLocalization.eq_iff_exists (.powers e)]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨n, hn⟩ := c.property
    change e ^ n = (c : R) at hn
    have hc' : e ^ n * x = e ^ n * y := by
      rw [hn]
      exact hc
    cases n with
    | zero =>
        have hxy : x = y := by simpa using hc'
        rw [hxy]
    | succ n => simpa [he.pow_succ_eq] using hc'
  · intro h
    exact ⟨⟨e, Submonoid.mem_powers e⟩, h⟩

/-- A monic polynomial equation over an idempotent localization lifts to a
global monic equation with supported coefficient equalities and supported
vanishing. The two commuting squares are the only compatibility required
between the ambient and localized pairs of ring maps. -/
lemma exists_monic_lift_with_supported_equalities
    {A : Type*} {B : Type*} {Ae : Type*} {Be : Type*}
    [CommRing A] [CommRing B] [CommRing Ae] [CommRing Be]
    [Algebra A Ae] [Algebra B Be]
    (s t : A →+* B) (se te : Ae →+* Be)
    (e : A) (he : IsIdempotentElem e) (hst : s e = t e)
    [IsLocalization.Away e Ae] [IsLocalization.Away (s e) Be]
    (hs : (algebraMap B Be).comp s = se.comp (algebraMap A Ae))
    (ht : (algebraMap B Be).comp t = te.comp (algebraMap A Ae))
    (q : Ae[X]) (hqmonic : q.Monic)
    (hqcoeff : ∀ k, se (q.coeff k) = te (q.coeff k))
    (x : A) (hqeval : q.eval (algebraMap A Ae x) = 0) :
    ∃ p : A[X], p.Monic ∧ p.map (algebraMap A Ae) = q ∧
      (∀ k, s (e * p.coeff k) = t (e * p.coeff k)) ∧
      e * p.eval x = 0 := by
  have hsurjective : Function.Surjective (algebraMap A Ae) :=
    IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he
  have hqlifts : q ∈ Polynomial.lifts (algebraMap A Ae) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    exact hsurjective (q.coeff k)
  obtain ⟨p, hpmap, _, hpmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hqlifts hqmonic
  refine ⟨p, hpmonic, hpmap, ?_, ?_⟩
  · intro k
    have hpcoeff : algebraMap A Ae (p.coeff k) = q.coeff k := by
      have h := congr_arg (fun f : Ae[X] ↦ f.coeff k) hpmap
      simpa only [Polynomial.coeff_map] using h
    have hlocal : algebraMap B Be (s (p.coeff k)) =
        algebraMap B Be (t (p.coeff k)) := by
      calc
        algebraMap B Be (s (p.coeff k)) =
            se (algebraMap A Ae (p.coeff k)) :=
          DFunLike.congr_fun hs (p.coeff k)
        _ = se (q.coeff k) := by rw [hpcoeff]
        _ = te (q.coeff k) := hqcoeff k
        _ = te (algebraMap A Ae (p.coeff k)) := by rw [hpcoeff]
        _ = algebraMap B Be (t (p.coeff k)) :=
          (DFunLike.congr_fun ht (p.coeff k)).symm
    have hsupported : s e * s (p.coeff k) = s e * t (p.coeff k) :=
      (algebraMap_eq_iff_mul_eq_of_isIdempotentElem
        (s e) (he.map s) _ _).mp hlocal
    calc
      s (e * p.coeff k) = s e * s (p.coeff k) := map_mul s _ _
      _ = s e * t (p.coeff k) := hsupported
      _ = t e * t (p.coeff k) := by rw [hst]
      _ = t (e * p.coeff k) := (map_mul t _ _).symm
  · rw [← mul_zero e]
    apply (algebraMap_eq_iff_mul_eq_of_isIdempotentElem
      (R := A) (S := Ae) e he (p.eval x) 0).mp
    rw [map_zero]
    calc
      algebraMap A Ae (p.eval x) =
          (p.map (algebraMap A Ae)).eval (algebraMap A Ae x) := by
        rw [Polynomial.eval_map_apply]
      _ = q.eval (algebraMap A Ae x) := by rw [hpmap]
      _ = 0 := hqeval

end IsLocalization.Away

namespace AlgHom

universe uι uR uA uB uA' uB'

variable {ι : Type uι} [Fintype ι]
  {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- A commuting morphism between two pairs of algebra maps induces the
evident map between their equalizers. -/
@[expose] noncomputable def equalizerMapOfCommuting
    {A' : Type uA'} {B' : Type uB'} [CommRing A'] [CommRing B']
    [Algebra R A'] [Algebra R B']
    (s t : A →ₐ[R] B) (s' t' : A' →ₐ[R] B')
    (f : A →ₐ[R] A') (g : B →ₐ[R] B')
    (hs : g.comp s = s'.comp f) (ht : g.comp t = t'.comp f) :
    equalizer s t →ₐ[R] equalizer s' t' :=
  (f.comp (equalizer s t).val).codRestrict (equalizer s' t') fun x ↦ by
    change s' (f x.1) = t' (f x.1)
    calc
      s' (f x.1) = g (s x.1) := (DFunLike.congr_fun hs x.1).symm
      _ = g (t x.1) := congrArg g x.2
      _ = t' (f x.1) := DFunLike.congr_fun ht x.1

@[simp]
lemma coe_equalizerMapOfCommuting
    {A' : Type uA'} {B' : Type uB'} [CommRing A'] [CommRing B']
    [Algebra R A'] [Algebra R B']
    (s t : A →ₐ[R] B) (s' t' : A' →ₐ[R] B')
    (f : A →ₐ[R] A') (g : B →ₐ[R] B')
    (hs : g.comp s = s'.comp f) (ht : g.comp t = t'.comp f)
    (x : equalizer s t) :
    ((equalizerMapOfCommuting s t s' t' f g hs ht x : equalizer s' t') : A') =
      f x.1 :=
  rfl

/-- If a commuting morphism of pairs is obtained by localizing both source
rings away from the images of an invariant idempotent, then the induced map
between equalizers is the corresponding idempotent localization. -/
lemma equalizerMapOfCommuting_isLocalizationAway
    {A' : Type uA'} {B' : Type uB'} [CommRing A'] [CommRing B']
    [Algebra R A'] [Algebra R B'] [Algebra A A'] [Algebra B B']
    (s t : A →ₐ[R] B) (s' t' : A' →ₐ[R] B')
    (f : A →ₐ[R] A') (g : B →ₐ[R] B')
    (hf : f.toRingHom = algebraMap A A')
    (hg : g.toRingHom = algebraMap B B')
    (hs : g.comp s = s'.comp f) (ht : g.comp t = t'.comp f)
    (e : equalizer s t) (he : IsIdempotentElem e)
    [IsLocalization.Away e.1 A'] [IsLocalization.Away (s e.1) B'] :
    let φ := equalizerMapOfCommuting s t s' t' f g hs ht
    let _ : Algebra (equalizer s t) (equalizer s' t') :=
      φ.toRingHom.toAlgebra
    IsLocalization.Away e (equalizer s' t') := by
  let φ := equalizerMapOfCommuting s t s' t' f g hs ht
  let _ : Algebra (equalizer s t) (equalizer s' t') :=
    φ.toRingHom.toAlgebra
  apply IsLocalization.away_of_isIdempotentElem_of_mul he
  · intro x y
    change φ x = φ y ↔ e * x = e * y
    rw [Subtype.ext_iff, Subtype.ext_iff]
    change f.toRingHom x.1 = f.toRingHom y.1 ↔ e.1 * x.1 = e.1 * y.1
    rw [hf]
    exact IsLocalization.Away.algebraMap_eq_iff_mul_eq_of_isIdempotentElem
      e.1 (he.map (equalizer s t).val) x.1 y.1
  · intro z
    have hsurj : Function.Surjective (algebraMap A A') :=
      IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem
        e.1 (he.map (equalizer s t).val)
    obtain ⟨x, hx⟩ := hsurj z.1
    have hlocal : algebraMap B B' (s x) = algebraMap B B' (t x) := by
      rw [← hg]
      have hx' : f x = z.1 := by
        change f.toRingHom x = z.1
        rw [hf]
        exact hx
      calc
        g (s x) = s' (f x) := DFunLike.congr_fun hs x
        _ = s' z.1 := by rw [hx']
        _ = t' z.1 := z.2
        _ = t' (f x) := by rw [hx']
        _ = g (t x) := (DFunLike.congr_fun ht x).symm
    have hsupported : s (e.1 * x) = t (e.1 * x) := by
      have hmul : s e.1 * s x = s e.1 * t x :=
        (IsLocalization.Away.algebraMap_eq_iff_mul_eq_of_isIdempotentElem
          (s e.1) (he.map (s.comp (equalizer s t).val)) (s x) (t x)).mp hlocal
      calc
        s (e.1 * x) = s e.1 * s x := map_mul s e.1 x
        _ = s e.1 * t x := hmul
        _ = t e.1 * t x := by rw [e.2]
        _ = t (e.1 * x) := (map_mul t e.1 x).symm
    let y : equalizer s t := ⟨e.1 * x, hsupported⟩
    refine ⟨y, Subtype.ext ?_⟩
    change f.toRingHom (e.1 * x) = z.1
    rw [hf]
    calc
      algebraMap A A' (e.1 * x) = algebraMap A A' x :=
        (IsLocalization.Away.algebraMap_eq_iff_mul_eq_of_isIdempotentElem
          e.1 (he.map (equalizer s t).val) (e.1 * x) x).mpr (by
            have heA : e.1 * e.1 = e.1 := congrArg Subtype.val he.eq
            calc
              e.1 * (e.1 * x) = (e.1 * e.1) * x := (mul_assoc _ _ _).symm
              _ = e.1 * x := by rw [heA])
      _ = z.1 := hx

/-- Finitely many idempotent-supported monic equations whose supported
coefficients lie in the equalizer of `s` and `t` patch to one monic equation
over that equalizer. This isolates the patching after invariant rank pieces
in Stacks Project, Lemmas 39.23.3–39.23.4 (tags 03BI, 03BJ); it does not
construct the norm equations of the latter. Orthogonality is not required:
idempotence of each piece and completeness of their sum suffice. -/
theorem isIntegral_equalizer_of_idempotent_polynomial_patches
    (s t : A →ₐ[R] B) (e : ι → A)
    (he : ∀ i, IsIdempotentElem (e i))
    (hcomplete : ∑ i, e i = 1)
    (x : A) (p : ι → A[X])
    (hpmonic : ∀ i, (p i).Monic)
    (hcoeff : ∀ i k,
      s (e i * (p i).coeff k) = t (e i * (p i).coeff k))
    (heval : ∀ i, e i * (p i).eval x = 0) :
    IsIntegral (equalizer s t) x := by
  classical
  let q : ι → A[X] := fun i ↦
    Polynomial.C (e i) * p i +
      Polynomial.C (1 - e i) * Polynomial.X ^ (p i).natDegree
  have hqcoeff_formula (i : ι) (k : ℕ) :
      (q i).coeff k = e i * (p i).coeff k +
        (1 - e i) * if k = (p i).natDegree then 1 else 0 := by
    simp only [q, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow]
  have hqmonic (i : ι) : (q i).Monic := by
    apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one (p i).natDegree
    · exact (Polynomial.natDegree_add_le _ _).trans (max_le
        (Polynomial.natDegree_C_mul_le _ _ |>.trans le_rfl)
        (Polynomial.natDegree_C_mul_le _ _ |>.trans
          (Polynomial.natDegree_X_pow_le _)))
    · rw [hqcoeff_formula]
      simp [hpmonic i |>.coeff_natDegree]
  have hqcoeff (i : ι) (k : ℕ) :
      s ((q i).coeff k) = t ((q i).coeff k) := by
    rw [hqcoeff_formula]
    by_cases hk : k = (p i).natDegree
    · subst k
      simp [hpmonic i |>.coeff_natDegree]
    · simpa [hk] using hcoeff i k
  have hqeval (i : ι) : e i * (q i).eval x = 0 := by
    simpa only [q, Polynomial.eval_add, Polynomial.eval_C_mul,
      Polynomial.eval_X_pow, mul_add, ← mul_assoc, he i |>.eq,
      he i |>.mul_one_sub_self, zero_mul, add_zero] using heval i
  have hqlifts (i : ι) : q i ∈ Polynomial.lifts
      (algebraMap (equalizer s t) A) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    exact ⟨⟨(q i).coeff k, hqcoeff i k⟩, rfl⟩
  choose qE hqE_map _ hqE_monic using fun i ↦
    Polynomial.lifts_and_natDegree_eq_and_monic (hqlifts i) (hqmonic i)
  let Q : (equalizer s t)[X] := ∏ i, qE i
  refine ⟨Q, ?_, ?_⟩
  · exact Finset.prod_induction qE (fun f ↦ f.Monic)
      (fun _ _ hf hg ↦ hf.mul hg) Polynomial.monic_one
      (fun i _ ↦ hqE_monic i)
  · rw [Polynomial.eval₂_eq_eval_map]
    have hQmap : Q.map (algebraMap (equalizer s t) A) = ∏ i, q i := by
      dsimp only [Q]
      rw [Polynomial.map_prod]
      exact Finset.prod_congr rfl fun i _ ↦ hqE_map i
    rw [hQmap, Polynomial.eval_prod]
    let z : A := ∏ i, (q i).eval x
    have hz (i : ι) : e i * z = 0 := by
      obtain ⟨z', hz'⟩ := Finset.dvd_prod_of_mem
        (fun j ↦ (q j).eval x) (Finset.mem_univ i)
      change e i * ∏ j, (q j).eval x = 0
      rw [hz']
      calc
        e i * ((q i).eval x * z') =
            (e i * (q i).eval x) * z' := by ring
        _ = 0 := by rw [hqeval i, zero_mul]
    change z = 0
    calc
      z = 1 * z := by rw [one_mul]
      _ = (∑ i, e i) * z := by rw [hcomplete]
      _ = ∑ i, e i * z := by rw [Finset.sum_mul]
      _ = 0 := by simp [hz]

end AlgHom
