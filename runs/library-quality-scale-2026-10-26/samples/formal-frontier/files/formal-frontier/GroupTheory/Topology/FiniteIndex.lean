/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Finite-index subgroups of compact commutative groups

A dense finitely generated subgroup of a compact Hausdorff commutative group makes
every positive-power image have finite index. The image is then open, and every
abstract finite-index subgroup is open without a closedness assumption.
The additive statements use natural-number scalar multiplication instead of powers.

Unlike abstract finite generation of the ambient group, dense finite generation
does not imply that its underlying group is finitely generated.

## References

* Neukirch, Schmidt, and Wingberg, *Cohomology of Number Fields*, Chapter I, §1,
  for the finite-index openness argument in the profinite abelian setting.
* Mathlib's finite-generation and torsion-finiteness results for commutative groups,
  together with its canonical power homomorphisms and closed finite-index subgroup lemma.
-/

@[expose] public section

universe u

namespace Subgroup

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G]

/-- In a compact Hausdorff commutative group with a dense finitely generated subgroup,
the image of every positive power map has finite index. This extends Mathlib's
`Subgroup.finiteIndex_range_powMonoidHom_of_fg`, which instead assumes abstract finite
generation of the entire ambient group. The dense subgroup has finite image in the
quotient by the closed power range; that image is closed as well as dense, so it is
the whole quotient. -/
@[to_additive /-- In a compact Hausdorff commutative additive group with a dense finitely
generated subgroup, the image of every positive natural-number scalar map has finite
index. -/]
theorem finiteIndex_range_powMonoidHom_of_dense_fg (D : Subgroup G) (hfg : D.FG)
    (hdense : Dense (D : Set G)) {n : ℕ} (hn : 0 < n) :
    (powMonoidHom (α := G) n).range.FiniteIndex := by
  let P : Subgroup G := (powMonoidHom (α := G) n).range
  have hclosed : IsClosed (P : Set G) := by
    change IsClosed (Set.range fun g : G => g ^ n)
    exact (isCompact_range (continuous_pow n)).isClosed
  let quotientMap : D →* G ⧸ P := (QuotientGroup.mk' P).comp D.subtype
  have hrel : (D.map (powMonoidHom (α := G) n)).IsFiniteRelIndex D :=
    isFiniteRelIndex_map_powMonoidHom_of_fg hfg (Nat.ne_of_gt hn)
  have hmap_le : D.map (powMonoidHom (α := G) n) ≤ P := by
    rintro _ ⟨g, _, rfl⟩
    exact ⟨g, rfl⟩
  have hker : quotientMap.ker.FiniteIndex := by
    have hrelP : P.IsFiniteRelIndex D :=
      @isFiniteRelIndex_of_le_left G _ (D.map (powMonoidHom (α := G) n)) P D
        hrel hmap_le
    have hker_eq : quotientMap.ker = P.subgroupOf D := by
      ext g
      exact QuotientGroup.eq_one_iff (g : G)
    rw [hker_eq]
    exact isFiniteRelIndex_iff_finiteIndex.mp hrelP
  have hfiniteQuotientD : Finite (D ⧸ quotientMap.ker) :=
    finiteIndex_iff_finite_quotient.mp hker
  have hfiniteImage : Finite quotientMap.range :=
    @Finite.of_equiv _ _ hfiniteQuotientD
      (QuotientGroup.quotientKerEquivRange quotientMap).toEquiv
  have hfiniteRange : (Set.range (quotientMap : D → G ⧸ P)).Finite :=
    @Set.toFinite _ _ hfiniteImage
  have hclosedRange : IsClosed (Set.range (quotientMap : D → G ⧸ P)) :=
    @Set.Finite.isClosed _ _ (QuotientGroup.t1Space_iff.mpr hclosed) _ hfiniteRange
  have hdenseQuotient : DenseRange quotientMap := by
    change DenseRange ((QuotientGroup.mk' P : G →* G ⧸ P) ∘ ((↑) : D → G))
    exact (QuotientGroup.mk'_surjective P).denseRange.comp
      hdense.denseRange_val QuotientGroup.continuous_mk
  have hsurj : Function.Surjective quotientMap := by
    intro g
    have hg := hdenseQuotient g
    rw [hclosedRange.closure_eq] at hg
    exact hg
  have hfiniteQuotient : Finite (G ⧸ P) :=
    Set.finite_univ_iff.mp (by simpa only [hsurj.range_eq] using hfiniteRange)
  exact finiteIndex_iff_finite_quotient.mpr hfiniteQuotient

/-- The range of a positive power map is open when a finitely generated subgroup is dense. -/
@[to_additive /-- The range of a positive scalar map is open when a finitely generated
additive subgroup is dense. -/]
theorem isOpen_range_powMonoidHom_of_dense_fg (D : Subgroup G) (hfg : D.FG)
    (hdense : Dense (D : Set G)) {n : ℕ} (hn : 0 < n) :
    IsOpen ((powMonoidHom (α := G) n).range : Set G) := by
  have hclosed : IsClosed ((powMonoidHom (α := G) n).range : Set G) := by
    change IsClosed (Set.range fun g : G => g ^ n)
    exact (isCompact_range (continuous_pow n)).isClosed
  exact @Subgroup.isOpen_of_isClosed_of_finiteIndex G _ _ _
    (powMonoidHom (α := G) n).range
    (finiteIndex_range_powMonoidHom_of_dense_fg D hfg hdense hn) hclosed

/-- Every abstract finite-index subgroup of a compact Hausdorff commutative group
with a dense finitely generated subgroup is open; no closedness is assumed of it.
This extends the profinite abelian finite-index argument in Neukirch, Schmidt,
and Wingberg, *Cohomology of Number Fields*, Chapter I, §1. -/
@[to_additive /-- Every abstract finite-index additive subgroup of a compact Hausdorff
commutative additive group with a dense finitely generated subgroup is open. -/]
theorem isOpen_of_finiteIndex_of_dense_fg (D : Subgroup G) (hfg : D.FG)
    (hdense : Dense (D : Set G)) (H : Subgroup G) [H.FiniteIndex] :
    IsOpen (H : Set G) := by
  have hindex : 0 < H.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  apply Subgroup.isOpen_mono (H₁ := (powMonoidHom (α := G) H.index).range)
    (H₂ := H) ?_ (isOpen_range_powMonoidHom_of_dense_fg D hfg hdense hindex)
  rintro _ ⟨g, rfl⟩
  exact H.pow_index_mem g

end Subgroup

end
