/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.PolynomialRationalPointHeight
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Common zeros of finite polynomial families

Over an algebraically closed field, fewer polynomial equations than variables cannot
isolate a known common zero. Positive-degree homogeneous equations automatically
have the origin as a common zero, and hence also have a nonzero common zero under
the same strict cardinality bound.

The uniqueness bound uses mathlib's strong affine Nullstellensatz to make
the evaluation prime minimal over the ideal of the equations. Mathlib's
finite-generator Krull height bound then applies to the image of the family,
and `MvPolynomial.height_ker_eval` computes the evaluation prime's height.
The other two results use this bound and, for homogeneous equations, the
origin as an already known common zero.

## References

* The Stacks Project, [Theorem 10.34.1](https://stacks.math.columbia.edu/tag/00FV)
  (Hilbert's Nullstellensatz) and
  [Lemma 10.60.12](https://stacks.math.columbia.edu/tag/0BBZ)
  (Krull's height bound for a prime minimal over finitely many generators).
* The mathlib community, *Mathlib*, `Mathlib.RingTheory.Nullstellensatz` for
  `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`, and
  `Mathlib.RingTheory.Ideal.KrullsHeightTheorem` for
  `Ideal.height_le_card_of_mem_minimalPrimes_span_finset`, and
  `Mathlib.RingTheory.MvPolynomial.Homogeneous` for the vanishing of positive-degree
  homogeneous polynomials at the origin.
* `AlgebraicGroups.Algebra.PolynomialRationalPointHeight` for the height of
  the rational evaluation ideal used in the inequality.
-/

public section

set_option warningAsError true

noncomputable section

namespace MvPolynomial

universe u v w

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {σ : Type v} [Fintype σ] {ι : Type w} [Fintype ι]

/-- A finite polynomial family with exactly one common zero has at least as many
equations as variables. From Hilbert's Nullstellensatz and Krull's height
theorem (Stacks Project, Theorem 10.34.1 and Lemma 10.60.12), using mathlib's
`vanishingIdeal_zeroLocus_eq_radical` and finite-generator height bound on
the prime minimal over the family's ideal. Repetitions and zero polynomials
are permitted. -/
theorem card_le_card_of_unique_common_zero (f : ι → MvPolynomial σ K) (a : σ → K)
    (hunique : ∀ x : σ → K, (∀ i, eval x (f i) = 0) ↔ x = a) :
    Fintype.card σ ≤ Fintype.card ι := by
  classical
  let J : Ideal (MvPolynomial σ K) := Ideal.span (Set.range f)
  have hzero : zeroLocus K J = {a} := by
    change zeroLocus K (Ideal.span (Set.range f)) = {a}
    rw [zeroLocus_span]
    ext x
    change (∀ p ∈ Set.range f, aeval x p = 0) ↔ x = a
    simpa only [Set.forall_mem_range, aeval_eq_eval] using hunique x
  have hker : vanishingIdeal K {a} = RingHom.ker (eval a) := by
    ext p
    simp only [mem_vanishingIdeal_singleton_iff, RingHom.mem_ker]
    rfl
  have hmin : vanishingIdeal K {a} ∈ J.minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes,
      ← vanishingIdeal_zeroLocus_eq_radical (K := K) J, hzero,
      Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  have hheight : (vanishingIdeal K {a}).height ≤ (Finset.univ.image f).card := by
    apply Ideal.height_le_card_of_mem_minimalPrimes_span_finset
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using hmin
  rw [hker, height_ker_eval K σ a] at hheight
  exact ENat.natCast_le_natCast.mp
    (hheight.trans (by exact_mod_cast Finset.card_image_le (s := Finset.univ) (f := f)))

/-- If a finite family has fewer equations than variables, any known common zero
has another distinct common zero. This is the contrapositive of the
Nullstellensatz-and-Krull-height bound `card_le_card_of_unique_common_zero`
(Stacks Project, Theorem 10.34.1 and Lemma 10.60.12); the supplied zero is
essential for arbitrary equations. -/
theorem exists_common_zero_ne (f : ι → MvPolynomial σ K) (a : σ → K)
    (hcard : Fintype.card ι < Fintype.card σ)
    (ha : ∀ i, eval a (f i) = 0) :
    ∃ x : σ → K, x ≠ a ∧ ∀ i, eval x (f i) = 0 := by
  by_contra hn
  have hunique (x : σ → K) : (∀ i, eval x (f i) = 0) ↔ x = a := by
    constructor
    · intro hx
      by_contra hne
      exact hn ⟨x, hne, hx⟩
    · rintro rfl
      exact ha
  exact (not_le_of_gt hcard) (card_le_card_of_unique_common_zero f a hunique)

/-- Fewer positive-degree homogeneous equations than variables have a nonzero
common zero. Positive homogeneity makes the origin a known zero; the
Nullstellensatz-and-Krull-height consequence `exists_common_zero_ne` supplies
another (Stacks Project, Theorem 10.34.1 and Lemma 10.60.12). Mathlib's
`IsHomogeneous.coeff_eq_zero` handles the origin. Degree labels can differ and
zero equations are allowed. -/
theorem exists_nonzero_common_zero_of_isHomogeneous (f : ι → MvPolynomial σ K)
    (d : ι → ℕ) (hcard : Fintype.card ι < Fintype.card σ)
    (hpositive : ∀ i, 0 < d i) (hhomo : ∀ i, (f i).IsHomogeneous (d i)) :
    ∃ x : σ → K, x ≠ 0 ∧ ∀ i, eval x (f i) = 0 := by
  apply exists_common_zero_ne f (0 : σ → K) hcard
  intro i
  rw [eval_zero, constantCoeff_eq]
  exact (hhomo i).coeff_eq_zero (by simpa using (hpositive i).ne)

end MvPolynomial
