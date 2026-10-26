/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Monic coprimeness under coefficient maps

For commutative rings in independent universes, the default-index resultant of a monic
polynomial and an arbitrary polynomial commutes with coefficient mapping. Only the monic
polynomial's degree must be preserved: Mathlib's right-index padding formula absorbs any
degree loss of the second polynomial. A zero target is handled separately.

Consequently a scalar unit-reflecting map reflects Bézout coprimeness when the first
polynomial is monic. Neither coefficient ring need be local or nontrivial, and the second
polynomial need not be monic. The proof uses Mathlib's fixed-index resultant mapping,
right-index padding, one-monic unit criterion and scalar unit reflection; it does not
assume that the induced polynomial map reflects units.

On monic field inputs this criterion agrees, by proof irrelevance, with
`Polynomial.isCoprime_map`. The latter also handles nonmonic first polynomials over fields;
the result here does not subsume those inputs.
-/

@[expose] public section

namespace Polynomial

/-- For a monic first polynomial, mapping both polynomials commutes with the resultant at
its default degree indices, even if the second polynomial loses degree. -/
theorem Monic.resultant_map_map
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) {p q : R[X]} (hp : p.Monic) :
    resultant (p.map φ) (q.map φ) = φ (resultant p q) := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · letI := hS
    exact Subsingleton.elim _ _
  letI := hS
  have hdegree : (q.map φ).natDegree ≤ q.natDegree := natDegree_map_le
  have hcoeff : (p.map φ).coeff p.natDegree = 1 := by
    rw [coeff_map, hp.coeff_natDegree, map_one]
  have hindex : (q.map φ).natDegree + (q.natDegree - (q.map φ).natDegree) =
      q.natDegree := by
    rw [Nat.add_comm, Nat.sub_add_cancel hdegree]
  have hpadding := resultant_add_right_deg (p.map φ) (q.map φ) p.natDegree
    (q.map φ).natDegree (q.natDegree - (q.map φ).natDegree) le_rfl
  rw [hindex, hcoeff, one_pow, one_mul] at hpadding
  calc
    resultant (p.map φ) (q.map φ) =
        resultant (p.map φ) (q.map φ) p.natDegree (q.map φ).natDegree := by
      rw [hp.natDegree_map φ]
    _ = resultant (p.map φ) (q.map φ) p.natDegree q.natDegree := hpadding.symm
    _ = φ (resultant p q) := Polynomial.resultant_map_map p q _ _ φ

/-- A scalar unit-reflecting coefficient map preserves and reflects Bézout coprimeness
when the first polynomial is monic. No monicity of the second polynomial is required. -/
theorem Monic.isCoprime_map_iff
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) [IsLocalHom φ] {p q : R[X]} (hp : p.Monic) :
    IsCoprime (p.map φ) (q.map φ) ↔ IsCoprime p q := by
  constructor
  · intro h
    apply (isUnit_resultant_iff_isCoprime hp).mp
    apply IsUnit.of_map φ (resultant p q)
    rw [← hp.resultant_map_map φ]
    exact (isUnit_resultant_iff_isCoprime (hp.map φ)).mpr h
  · intro h
    exact h.map (mapRingHom φ)

/-- On monic field inputs the unit-reflecting criterion and `Polynomial.isCoprime_map`
prove the same oriented proposition, so their proofs agree by proof irrelevance. Scalar
unit reflection is supplied by Mathlib's field-map instance. This is only their monic
overlap, not the unrestricted field API. -/
theorem Monic.isCoprime_map_iff_eq_isCoprime_map
    {K : Type*} {L : Type*} [Field K] [Field L]
    (φ : K →+* L) {p q : K[X]} (hp : p.Monic) :
    hp.isCoprime_map_iff (q := q) φ =
      Polynomial.isCoprime_map (p := p) (q := q) φ :=
  Subsingleton.elim _ _

end Polynomial
