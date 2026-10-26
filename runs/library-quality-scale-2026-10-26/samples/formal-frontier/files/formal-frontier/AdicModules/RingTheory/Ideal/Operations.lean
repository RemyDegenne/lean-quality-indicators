/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Comaximality, powers and scalar images of ideals

If `J ⊔ I = ⊤`, then `J ⊔ I ^ n = ⊤` for every natural exponent,
where `J` and `I` are arbitrary left ideals of a semiring. The semiring may
be noncommutative and need not have additive inverses or multiplication
cancellation. Neither ideal is required to be two-sided. Powers are formed
as ideals in the original semiring, not as spans of powers of chosen generators.

The proof uses a subtraction-free geometric-sum recurrence. Starting with
`j + i = 1`, where `j ∈ J` and `i ∈ I`, it constructs `x ∈ J` with
`x + i ^ n = 1`. The successor step replaces `x` by `x + i ^ n * j`,
using only closure of `J` under left multiplication.

The two-sided specializations recover Mathlib's comaximal-power statements
under their respective two-sidedness hypotheses.

For comaximal ideals `I` and `J` of a commutative semiring and any submodule `N`,
the ideal-generated scalar images satisfy `(I ⊓ J) • N = (I • N) ⊓ (J • N)`.
The action consists of finite sums of scalar multiples; the module needs only
an additive commutative monoid structure. Writing `1 = s + t` with `s ∈ I`
and `t ∈ J` splits any element of both images into two terms in the common
image, using Mathlib's comaximal ideal product and associative action APIs.

For a finite selection `s` of pairwise comaximal ideals, the scalar image of
`⨅ i ∈ s, I i` is `N ⊓ (⨅ i ∈ s, I i • N)`. The factor `N` includes the empty
selection, for which both indexed intersections are top. The proof iterates the
binary scalar-image theorem, using Mathlib's finite sup-intersection theorem.
The ambient index type is arbitrary and may lie in a third universe.

## References

* Mathlib's left-ideal operations, power and ideal-on-submodule action APIs in
  `Mathlib.RingTheory.Ideal.Operations`, authored by Kenny Lau. The scalar-image
  intersection proof uses `Ideal.mul_eq_inf_of_coprime` and `Submodule.mul_smul`.
  The finite-family proof reuses the binary theorem below and Mathlib's
  `Ideal.sup_iInf_eq_top` (with automatic two-sidedness over a commutative semiring).
* `Ideal.sup_pow_eq_top` and `Ideal.sup_pow_eq_top'` in that module give
  comaximal-power results when the unpowered or powered ideal, respectively,
  is two-sided.
* Neil Strickland's geometric-sum identities in `Mathlib.Algebra.Ring.GeomSum`.
  The recurrence here avoids both subtraction and a commutation assumption.
-/

@[expose] public section

universe u
universe v
universe w

namespace Ideal

/-- Comaximal left ideals remain comaximal after taking any natural power of
one of them. This extends Mathlib's `Ideal.sup_pow_eq_top` and
`Ideal.sup_pow_eq_top'` without requiring either ideal to be two-sided.
The proof uses a subtraction-free geometric-sum recurrence. -/
theorem sup_pow_eq_top_of_sup_eq_top {R : Type u} [Semiring R]
    {J I : Ideal R} {n : ℕ} (h : J ⊔ I = ⊤) : J ⊔ I ^ n = ⊤ := by
  obtain ⟨j, hj, i, hi, hji⟩ :=
    Submodule.mem_sup.mp ((eq_top_iff_one _).mp h)
  have hp : ∃ x ∈ J, x + i ^ n = 1 := by
    induction n with
    | zero => exact ⟨0, J.zero_mem, by rw [pow_zero, zero_add]⟩
    | succ n ih =>
      obtain ⟨x, hx, hxi⟩ := ih
      refine ⟨x + i ^ n * j, J.add_mem hx (J.mul_mem_left _ hj), ?_⟩
      calc
        (x + i ^ n * j) + i ^ (n + 1) = x + i ^ n * (j + i) := by
          rw [pow_succ, mul_add, add_assoc]
        _ = x + i ^ n := by rw [hji, mul_one]
        _ = 1 := hxi
  obtain ⟨x, hx, hxi⟩ := hp
  exact (eq_top_iff_one _).mpr
    (Submodule.mem_sup.mpr ⟨x, hx, i ^ n, pow_mem_pow hi n, hxi⟩)

/-- Independent natural powers of pairwise comaximal left ideals remain
pairwise comaximal, including at exponent zero. No finiteness or two-sidedness
assumption is needed. -/
theorem pairwise_sup_eq_top_pow
    {R : Type u} {ι : Type v} [Semiring R]
    (I : ι → Ideal R)
    (hI : Pairwise (fun i j => I i ⊔ I j = ⊤)) (n : ι → ℕ) :
    Pairwise (fun i j => I i ^ n i ⊔ I j ^ n j = ⊤) := by
  intro i j hij
  have h : I j ^ n j ⊔ I i = ⊤ :=
    (sup_comm _ _).trans (sup_pow_eq_top_of_sup_eq_top (n := n j) (hI hij))
  exact (sup_comm _ _).trans (sup_pow_eq_top_of_sup_eq_top (n := n i) h)

/-- The comaximal-power conclusion when the unpowered ideal is two-sided. -/
private theorem sup_pow_eq_top_of_isTwoSided_left
    {R : Type u} [Semiring R] {I J : Ideal R} [I.IsTwoSided] {n : ℕ}
    (h : I ⊔ J = ⊤) : I ⊔ J ^ n = ⊤ :=
  sup_pow_eq_top_of_sup_eq_top (J := I) (I := J) (n := n) h

/-- The comaximal-power conclusion when the powered ideal is two-sided. -/
private theorem sup_pow_eq_top_of_isTwoSided_right
    {R : Type u} [Semiring R] {I J : Ideal R} [J.IsTwoSided] {n : ℕ}
    (h : I ⊔ J = ⊤) : I ⊔ J ^ n = ⊤ :=
  sup_pow_eq_top_of_sup_eq_top (J := I) (I := J) (n := n) h

end Ideal

namespace Submodule

/-- The scalar images of comaximal ideals intersect in the image of their
intersection, on any submodule over a commutative semiring. The ideal action
is generated by finite sums of scalar multiples. The proof uses Mathlib's
`Ideal.mul_eq_inf_of_coprime` and `Submodule.mul_smul`, without additive inverses. -/
theorem ideal_smul_inf_of_sup_eq_top
    {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]
    {I J : Ideal R} (N : Submodule R M) (hIJ : I ⊔ J = ⊤) :
    (I ⊓ J) • N = (I • N) ⊓ (J • N) := by
  refine le_antisymm
    (le_inf (smul_mono_left inf_le_left) (smul_mono_left inf_le_right)) ?_
  rintro x ⟨hxI, hxJ⟩
  obtain ⟨s, hs, t, ht, hst⟩ :=
    mem_sup.mp ((Ideal.eq_top_iff_one _).mp hIJ)
  have hsx : s • x ∈ (I ⊓ J) • N := by
    rw [← Ideal.mul_eq_inf_of_coprime hIJ, Submodule.mul_smul]
    exact smul_mem_smul hs hxJ
  have htx : t • x ∈ (I ⊓ J) • N := by
    rw [inf_comm, ← Ideal.mul_eq_inf_of_coprime ((sup_comm J I).trans hIJ),
      Submodule.mul_smul]
    exact smul_mem_smul ht hxI
  have hsum := ((I ⊓ J) • N).add_mem hsx htx
  rwa [← add_smul, hst, one_smul] at hsum

/-- The scalar image of a finite intersection of pairwise comaximal ideals is
`N` intersected with the intersection of their scalar images. Comaximality is
required only on the selected finite set; the ambient index type is arbitrary.
The factor `N` is essential for the empty selection, whose intersection is top.
The proof iterates `ideal_smul_inf_of_sup_eq_top`, using Mathlib's
`Ideal.sup_iInf_eq_top` for comaximality with the remaining intersection. -/
theorem ideal_smul_iInf_of_pairwise_sup_eq_top
    {R : Type u} {M : Type v} {ι : Type w}
    [CommSemiring R] [AddCommMonoid M] [Module R M]
    (I : ι → Ideal R) (s : Finset ι) (N : Submodule R M)
    (hI : (s : Set ι).Pairwise (fun i j => I i ⊔ I j = ⊤)) :
    (⨅ i ∈ s, I i) • N = N ⊓ (⨅ i ∈ s, I i • N) := by
  classical
  revert hI
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp
  | @insert a t ha ih =>
      intro hI
      have ht : (t : Set ι).Pairwise (fun i j => I i ⊔ I j = ⊤) := by
        intro i hi j hj hij
        exact hI (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij
      have hat : I a ⊔ (⨅ i ∈ t, I i) = ⊤ := by
        apply Ideal.sup_iInf_eq_top
        intro i hi
        exact hI (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hi)
          (fun hai => ha (hai.symm ▸ hi))
      simp only [Finset.iInf_insert]
      rw [ideal_smul_inf_of_sup_eq_top N hat, ih ht, inf_left_comm]

end Submodule
