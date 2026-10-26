/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import AlgebraicGroups.Category.EquivalenceRelation

@[expose] public section

/-!
# Rank strata of finite flat equivalence relations

For an internal equivalence relation in schemes whose first projection is
finite and flat, the two projections have the same rank and that rank is
constant along relation arrows.  When the projection is locally of finite
presentation, the rank fibres are clopen invariant opens.  The rank is
positive, and on a compact target only finitely many ranks occur.

This is the reusable rank-stratum input for finite locally free descent.  It
does not construct an affine quotient or prove effectivity.

Pointwise rank invariance compares the composition pullback with the defining
pullback of the internal equivalence relation. Finite flatness suffices;
local finite presentation gives clopen rank fibres, compactness gives a finite
range, and reflexivity gives positive rank at every target point. Empty
schemes and unused rank-zero pieces require no exception.

## References

* The Stacks Project, Lemma 39.23.3
  ([tag 03BI](https://stacks.math.columbia.edu/tag/03BI)), gives the
  invariant constant-rank decomposition of a finite locally free groupoid.
* Mathlib, `Mathlib.AlgebraicGeometry.Morphisms.FlatRank`, supplies
  `Scheme.Hom.finrank_of_isPullback`, `one_le_finrank_iff_surjective` and
  `isLocallyConstant_finrank`. `AlgebraicGroups.Category.EquivalenceRelation`
  supplies the composition pullback and symmetry used here.
-/

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.EquivalenceRelation

universe u

variable {R X : Scheme.{u}} {p₁ p₂ : R ⟶ X}

/-- The second projection of a finite internal equivalence relation is finite
whenever the first projection is. -/
lemma isFinite_snd [IsFinite p₁]
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) :
    IsFinite p₂ := by
  let _ : IsIso h.s :=
    CategoryTheory.EquivalenceRelation.isIso_symmetry h
  rw [← h.symmetry₁]
  infer_instance

/-- The second projection of a flat internal equivalence relation is flat
whenever the first projection is. -/
lemma flat_snd [Flat p₁]
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) :
    Flat p₂ := by
  let _ : IsIso h.s :=
    CategoryTheory.EquivalenceRelation.isIso_symmetry h
  rw [← h.symmetry₁]
  infer_instance

/-- Local finite presentation transfers from the first projection of an
internal equivalence relation to the second. -/
lemma locallyOfFinitePresentation_snd [LocallyOfFinitePresentation p₁]
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) :
    LocallyOfFinitePresentation p₂ := by
  let _ : IsIso h.s :=
    CategoryTheory.EquivalenceRelation.isIso_symmetry h
  rw [← h.symmetry₁]
  infer_instance

variable [Flat p₁] [IsFinite p₁]

/-- The second projection has the same rank function as the first, since the
symmetry map identifies it with precomposition by an isomorphism. -/
lemma finrank_snd_eq_finrank_fst
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) :
    p₂.finrank = p₁.finrank := by
  let _ : IsIso h.s :=
    CategoryTheory.EquivalenceRelation.isIso_symmetry h
  rw [← h.symmetry₁]
  exact Scheme.Hom.finrank_comp_left_of_isIso h.s p₁

/-- The rank of the first projection is constant along relation arrows, by
the two pullback rank comparisons in the argument of Stacks Project
[Lemma 39.23.3, tag 03BI](https://stacks.math.columbia.edu/tag/03BI).
No quotient or effectivity hypothesis is used. -/
lemma finrank_fst_eq_finrank_snd
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) (z : R) :
    p₁.finrank (p₁ z) = p₁.finrank (p₂ z) := by
  have hcomposition : IsPullback h.t h.c.fst p₁ p₁ :=
    IsPullback.of_isLimit
      (CategoryTheory.EquivalenceRelation.isLimit_composition_fst h)
  have hleft : h.c.fst.finrank z = p₁.finrank (p₁ z) :=
    Scheme.Hom.finrank_of_isPullback h.t h.c.fst p₁ p₁ hcomposition z
  have hrelation : IsPullback h.c.snd h.c.fst p₁ p₂ :=
    IsPullback.of_isLimit (PullbackCone.flipIsLimit h.isLimit)
  have hright : h.c.fst.finrank z = p₁.finrank (p₂ z) :=
    Scheme.Hom.finrank_of_isPullback h.c.snd h.c.fst p₁ p₂ hrelation z
  exact hleft.symm.trans hright

/-- Every rank fibre of a finite flat locally finitely presented morphism is
clopen. -/
lemma isClopen_finrank_fiber [LocallyOfFinitePresentation p₁] (r : ℕ) :
    IsClopen {x : X | p₁.finrank x = r} :=
  p₁.isLocallyConstant_finrank.isClopen_fiber r

/-- Membership in a rank fibre is invariant under the two relation maps. -/
lemma finrank_fiber_invariant
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) (r : ℕ) (z : R) :
    p₁ z ∈ {x : X | p₁.finrank x = r} ↔
      p₂ z ∈ {x : X | p₁.finrank x = r} := by
  change p₁.finrank (p₁ z) = r ↔ p₁.finrank (p₂ z) = r
  rw [finrank_fst_eq_finrank_snd h z]

/-- The rank-`r` fibre as an open subset of the target. This packages the
rank pieces of Stacks Project
[Lemma 39.23.3, tag 03BI](https://stacks.math.columbia.edu/tag/03BI)
under the explicit local finite presentation hypothesis. -/
def finrankOpen [LocallyOfFinitePresentation p₁] (r : ℕ) : X.Opens :=
  ⟨{x : X | p₁.finrank x = r}, (isClopen_finrank_fiber (p₁ := p₁) r).2⟩

@[simp]
lemma mem_finrankOpen [LocallyOfFinitePresentation p₁] (r : ℕ) (x : X) :
    x ∈ finrankOpen (p₁ := p₁) r ↔ p₁.finrank x = r :=
  Iff.rfl

/-- Invariance identifies the two open preimages of a rank stratum. -/
lemma preimage_finrankOpen_eq [LocallyOfFinitePresentation p₁]
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) (r : ℕ) :
    p₁ ⁻¹ᵁ finrankOpen (p₁ := p₁) r =
      p₂ ⁻¹ᵁ finrankOpen (p₁ := p₁) r := by
  ext z
  exact finrank_fiber_invariant h r z

/-- Reflexivity makes either projection surjective, hence the rank of the
first projection is everywhere positive. -/
lemma one_le_finrank
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) (x : X) :
    1 ≤ p₁.finrank x := by
  have hsurjective : Surjective p₁ :=
    ⟨fun y ↦ ⟨h.r y, by
      rw [← Scheme.Hom.comp_apply, h.reflexivity₁]
      rfl⟩⟩
  exact (Scheme.Hom.one_le_finrank_iff_surjective p₁).2 hsurjective x

/-- The rank-zero fibre of either projection is empty. -/
lemma finrank_zero_fiber_eq_empty
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) :
    {x : X | p₁.finrank x = 0} = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro x hx
  have hxpos := one_le_finrank h x
  rw [hx] at hxpos
  omega

/-- On a compact target, only finitely many ranks occur. -/
lemma finite_range_finrank [LocallyOfFinitePresentation p₁] [CompactSpace X] :
    (Set.range p₁.finrank).Finite :=
  p₁.isLocallyConstant_finrank.range_finite

/-- The canonical finite indexing type of ranks occurring on a compact
target. -/
@[instance_reducible]
noncomputable def finrankRangeFintype [LocallyOfFinitePresentation p₁]
    [CompactSpace X] : Fintype (Set.range p₁.finrank) :=
  (finite_range_finrank (p₁ := p₁)).fintype

end AlgebraicGeometry.EquivalenceRelation
