/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.Tactic.Ring.Basic
public import ToricIdeals.RationalNormalCurve

/-!
# Formal smoothness of rational-normal-curve coordinate rings

The full Hankel quotient is formally smooth over its coefficient ring exactly
when the degree is at most one or the coefficient ring is a zero ring.
The algebra structure is the canonical coefficient algebra structure.

At degree zero the Hankel ideal is bottom, so the quotient is the full
one-variable polynomial ring, not the parametrization image. At degree one it
is the full two-variable polynomial ring. The criterion includes arbitrary
commutative coefficient rings, including characteristic two and zero rings.
-/

@[expose] public section

namespace ToricIdeals.RationalNormalCurve

universe u

/-- The relation in the first two columns obstructs a lift across the
square-zero ideal `(t²)` in `R[t]/(t³)`. -/
private theorem not_formallySmooth_quotient_of_two_le (R : Type u) [CommRing R]
    [Nontrivial R] (n : ℕ) (hn : 2 ≤ n) :
    ¬ Algebra.FormallySmooth R (Source R n ⧸ hankelIdeal R n) := by
  intro h
  let := h
  let B := AdjoinRoot ((Polynomial.X : Polynomial R) ^ 3)
  let t : B := AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ 3)
  have ht3 : t ^ 3 = 0 := by
    rw [← AdjoinRoot.eval₂_root, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  have ht2 : t ^ 2 ≠ 0 := by
    intro ht
    apply AdjoinRoot.mk_ne_zero_of_natDegree_lt
      (f := (Polynomial.X : Polynomial R) ^ 3) (Polynomial.monic_X_pow 3)
      (g := (Polynomial.X : Polynomial R) ^ 2) (Polynomial.monic_X_pow 2).ne_zero
      (by simp only [Polynomial.natDegree_X_pow]; decide)
    rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_X_pow]
    exact ht
  have ht4 : t ^ 4 = 0 := by
    calc
      t ^ 4 = t ^ 3 * t := by ring
      _ = 0 := by rw [ht3, zero_mul]
  let I : Ideal B := Ideal.span {t ^ 2}
  have hI : I ^ 2 = ⊥ := by
    dsimp [I]
    rw [Ideal.span_singleton_pow, ← pow_mul]
    change Ideal.span ({t ^ 4} : Set B) = ⊥
    rw [ht4, Ideal.span_singleton_zero]
  let e : B →ₐ[R] B ⧸ I := Ideal.Quotient.mkₐ R I
  have he2 : (e t) ^ 2 = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (t ^ 2))
  let v : Fin (n + 1) → B ⧸ I := fun i => if i.val = 1 then e t else 0
  have hv_mul (i j : Fin (n + 1)) : v i * v j = 0 := by
    by_cases hi : i.val = 1 <;> by_cases hj : j.val = 1 <;>
      simp [v, hi, hj, ← pow_two, he2]
  let φ : Source R n →ₐ[R] B ⧸ I := MvPolynomial.aeval v
  have hker : hankelIdeal R n ≤ RingHom.ker φ.toRingHom := by
    apply Ideal.span_le.2
    rintro _ ⟨p, rfl⟩
    change φ (hankelMinor R n p) = 0
    simp only [φ, hankelMinor, map_sub, map_mul, MvPolynomial.aeval_X, hv_mul, sub_self]
  let g : Source R n ⧸ hankelIdeal R n →ₐ[R] B ⧸ I :=
    Ideal.Quotient.liftₐ (hankelIdeal R n) φ (fun a ha => hker ha)
  obtain ⟨f, hf⟩ :=
    Algebra.FormallySmooth.comp_surjective R (Source R n ⧸ hankelIdeal R n) I hI g
  let q : Source R n →ₐ[R] Source R n ⧸ hankelIdeal R n :=
    Ideal.Quotient.mkₐ R (hankelIdeal R n)
  let F : Source R n →ₐ[R] B := f.comp q
  have hF : e.comp F = φ := by
    calc
      e.comp F = (e.comp f).comp q := rfl
      _ = g.comp q := by rw [hf]
      _ = φ := Ideal.Quotient.liftₐ_comp _ _ _
  have hFi (i : Fin (n + 1)) : e (F (MvPolynomial.X i)) = v i := by
    simpa only [AlgHom.comp_apply, φ, MvPolynomial.aeval_X] using
      DFunLike.congr_fun hF (MvPolynomial.X i)
  let c0 : Fin n := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hn⟩
  let c1 : Fin n := ⟨1, lt_of_lt_of_le (by decide : 1 < 2) hn⟩
  have hF0 : e (F (MvPolynomial.X c0.castSucc)) = 0 := by
    simpa [v, c0] using hFi c0.castSucc
  have hF1 : e (F (MvPolynomial.X c0.succ) - t) = 0 := by
    rw [map_sub, hFi]
    simp [v, c0]
  have hF2 : e (F (MvPolynomial.X c1.succ)) = 0 := by
    simpa [v, c1] using hFi c1.succ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp hF0)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp hF1)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp hF2)
  have hb' : F (MvPolynomial.X c0.succ) = b * t ^ 2 + t :=
    sub_eq_iff_eq_add.mp hb.symm
  let p : MinorIndex n := ⟨(c0, c1), by change (0 : ℕ) < 1; decide⟩
  have hi : c1.castSucc = c0.succ := by
    apply Fin.ext
    rfl
  have hrel : F (hankelMinor R n p) = 0 := by
    change f (q (hankelMinor R n p)) = 0
    have hq : q (hankelMinor R n p) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (minor_mem R n p)
    rw [hq, map_zero]
  have hrelation :
      F (MvPolynomial.X c0.castSucc) * F (MvPolynomial.X c1.succ) -
        F (MvPolynomial.X c0.succ) * F (MvPolynomial.X c0.succ) = 0 := by
    simpa only [hankelMinor, p, map_sub, map_mul, hi] using hrel
  rw [← ha, ← hc, hb'] at hrelation
  have hac : (a * t ^ 2) * (c * t ^ 2) = 0 := by
    calc
      (a * t ^ 2) * (c * t ^ 2) = (a * c) * t ^ 4 := by ring
      _ = 0 := by rw [ht4, mul_zero]
  have hbb : (b * t ^ 2 + t) * (b * t ^ 2 + t) = t ^ 2 := by
    calc
      (b * t ^ 2 + t) * (b * t ^ 2 + t) =
          b ^ 2 * t ^ 4 + (b + b) * t ^ 3 + t ^ 2 := by ring
      _ = t ^ 2 := by simp only [ht4, ht3, mul_zero, zero_add]
  rw [hac, hbb, zero_sub, neg_eq_zero] at hrelation
  exact ht2 hrelation

/-- The full Hankel quotient is formally smooth over its coefficient ring
exactly in degrees zero and one, or when the coefficient ring is a zero ring. -/
theorem quotient_formallySmooth_iff (R : Type u) [CommRing R] (n : ℕ) :
    Algebra.FormallySmooth R (Source R n ⧸ hankelIdeal R n) ↔
      n ≤ 1 ∨ Subsingleton R := by
  constructor
  · intro h
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inr hR
    · let : Nontrivial R := hR
      rcases le_or_gt n 1 with hn | hn
      · exact Or.inl hn
      · exact ((not_formallySmooth_quotient_of_two_le R n
          (Nat.succ_le_of_lt hn)) h).elim
  · rintro (hn | hR)
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
      · let e := (Ideal.quotientEquivAlgOfEq R (hankelIdeal_zero R)).trans
          (AlgEquiv.quotientBot R (Source R 0))
        exact Algebra.FormallySmooth.of_equiv e.symm
      · let e := (Ideal.quotientEquivAlgOfEq R (hankelIdeal_one R)).trans
          (AlgEquiv.quotientBot R (Source R 1))
        exact Algebra.FormallySmooth.of_equiv e.symm
    · let : Subsingleton R := hR
      let : Subsingleton (Source R n ⧸ hankelIdeal R n) :=
        Algebra.subsingleton R (Source R n ⧸ hankelIdeal R n)
      infer_instance

end ToricIdeals.RationalNormalCurve
