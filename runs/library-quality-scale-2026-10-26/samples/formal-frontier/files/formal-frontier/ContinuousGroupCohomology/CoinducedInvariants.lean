/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.QuotientInvariants
public import ContinuousGroupCohomology.Topology.ContinuousMap.CompactDiscrete

/-!
# Normal-subgroup invariants of twisted coinduction

For a normal subgroup `N` of a compact group `G`, the `N`-invariants of the twisted
coinduction of a discrete, jointly continuous representation on `B` are coinduced
from the **entire** carrier `B` with the trivial action of `G ⧸ N`. The forward
coordinate at `tN` untwists by `t⁻¹`; the inverse twists by `t`. The compact-open
topology on both function spaces is discrete, while continuity of the action in
both variables is a separate property.

## References

* Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Chapter I §3,
  Proposition (1.3.6)(ii), normal-invariants clause.
* Mathlib, `ContRepresentation.coind₁` and `TopRep.coind₁Functor`.
* ContinuousGroupCohomology, `TopRep.quotientInvariants` and
  `ContinuousMap.discreteTopology_of_compactSpace`.

The cited source assumes a closed normal subgroup of a profinite group and a
discrete module. Here no closedness, Hausdorffness, or total disconnectedness
of the compact topological group is required.
-/

@[expose] public section

universe u v w z

open CategoryTheory

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]

section TrivialMap

variable {G : Type v} [Monoid G]

/-- Every continuous linear coefficient map intertwines trivial group actions. -/
def trivialMap {H : Type z} [Monoid H] {B C : TopRep.{w} k G} (φ : B →L[k] C) :
    TopRep.of (ContRepresentation.trivial k H B) ⟶
      TopRep.of (ContRepresentation.trivial k H C) :=
  ofHom {
    toContinuousLinearMap := φ
    isIntertwining' := by
      intro h
      ext b
      rfl
  }

/-- The trivial-action coefficient map is the original continuous linear map. -/
@[simp] theorem trivialMap_apply {H : Type z} [Monoid H]
    {B C : TopRep.{w} k G} (φ : B →L[k] C) (b : B) :
    trivialMap (H := H) φ b = φ b := rfl

/-- The trivial-action construction carries identity coefficient maps to identities. -/
@[simp] theorem trivialMap_id {H : Type z} [Monoid H] (B : TopRep.{w} k G) :
    trivialMap (H := H) (ContinuousLinearMap.id k B) =
      𝟙 (TopRep.of (ContRepresentation.trivial k H B)) := by
  ext b
  rfl

/-- The trivial-action construction respects composition of coefficient maps. -/
theorem trivialMap_comp {H : Type z} [Monoid H] {B C D : TopRep.{w} k G}
    (φ : B →L[k] C) (ψ : C →L[k] D) :
    trivialMap (H := H) (ψ.comp φ) =
      trivialMap (H := H) φ ≫ trivialMap (H := H) ψ := by
  ext b
  rfl

end TrivialMap

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] (N : Subgroup G) [N.Normal]
variable (B : TopRep.{w} k G) [JointlyContinuous B]

omit [CompactSpace G] [JointlyContinuous B] in
/-- Untwisted evaluation of an invariant function depends only on its quotient coset. -/
theorem coind₁_untwist_eq_of_mk_eq
    (f : quotientInvariants N (coind₁ B)) {t s : G}
    (h : QuotientGroup.mk' N t = QuotientGroup.mk' N s) :
    B.ρ t⁻¹ (f.1 t) = B.ρ s⁻¹ (f.1 s) := by
  obtain ⟨n, hn, rfl⟩ := (QuotientGroup.mk'_eq_mk' N).mp h
  have hmem : t * n * t⁻¹ ∈ N := by
    simpa only [inv_inv] using
      (Subgroup.Normal.conj_mem' ‹N.Normal› n hn t⁻¹)
  have hfix := congrArg (fun h : C(G, B) => h (t * n))
    (f.2 ⟨t * n * t⁻¹, hmem⟩)
  change B.ρ (t * n * t⁻¹) (f.1 ((t * n * t⁻¹)⁻¹ * (t * n))) =
    f.1 (t * n) at hfix
  have ht : (t * n * t⁻¹)⁻¹ * (t * n) = t := by group
  rw [ht] at hfix
  calc
    B.ρ t⁻¹ (f.1 t) = B.ρ ((t * n)⁻¹ * (t * n * t⁻¹)) (f.1 t) := by
      congr 1
      group
    _ = B.ρ (t * n)⁻¹ (f.1 (t * n)) := by
      rw [map_mul]
      exact congrArg (fun b => B.ρ (t * n)⁻¹ b) hfix

omit [CompactSpace G] in
/-- Descend untwisted evaluation of an invariant coinduced function to the quotient. -/
def quotientCoind₁Forward
    (f : quotientInvariants N (coind₁ B)) : C(G ⧸ N, B) := by
  let forward : G ⧸ N → B := fun q =>
    Quotient.liftOn' q (fun t => B.ρ t⁻¹ (f.1 t))
      (fun t s h => coind₁_untwist_eq_of_mk_eq N B f (Quotient.sound h))
  refine ⟨forward, (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr ?_⟩
  change Continuous (fun t : G => B.ρ t⁻¹ (f.1 t))
  exact JointlyContinuous.continuous_action.comp
    (continuous_inv.prodMk f.1.continuous)

omit [CompactSpace G] in
/-- Forward quotient evaluation on a representative. -/
@[simp] theorem quotientCoind₁Forward_apply_mk
    (f : quotientInvariants N (coind₁ B)) (t : G) :
    quotientCoind₁Forward N B f (QuotientGroup.mk' N t) = B.ρ t⁻¹ (f.1 t) := rfl

omit [CompactSpace G] in
/-- Twist a quotient function into a coinduced function fixed by the normal subgroup. -/
def quotientCoind₁Backward
    (F : C(G ⧸ N, B)) : quotientInvariants N (coind₁ B) := by
  refine ⟨⟨fun t => B.ρ t (F (QuotientGroup.mk' N t)), ?_⟩, ?_⟩
  · exact JointlyContinuous.continuous_action.comp
      (continuous_id.prodMk (F.continuous.comp QuotientGroup.continuous_mk))
  · intro n
    ext t
    have hn : QuotientGroup.mk' N n.1 = 1 :=
      (QuotientGroup.eq_one_iff n.1).mpr n.2
    have heq : QuotientGroup.mk' N (n.1⁻¹ * t) = QuotientGroup.mk' N t := by
      rw [map_mul, map_inv, hn, inv_one, one_mul]
    change B.ρ n.1 (B.ρ (n.1⁻¹ * t)
      (F (QuotientGroup.mk' N (n.1⁻¹ * t)))) =
        B.ρ t (F (QuotientGroup.mk' N t))
    rw [heq]
    change ((B.ρ n.1) * (B.ρ (n.1⁻¹ * t))) (F (QuotientGroup.mk' N t)) =
      B.ρ t (F (QuotientGroup.mk' N t))
    rw [← map_mul]
    simp

omit [CompactSpace G] in
/-- Backward evaluation at a group element. -/
@[simp] theorem quotientCoind₁Backward_apply
    (F : C(G ⧸ N, B)) (t : G) :
    (quotientCoind₁Backward N B F).1 t = B.ρ t (F (QuotientGroup.mk' N t)) := rfl

/-- Canonical quotient representation of the normal invariants of twisted coinduction.
The coefficient on the right is all of `B` with trivial quotient action, not
the submodule of `N`-fixed vectors. This extends the normal-invariants clause
of Neukirch–Schmidt–Wingberg, I §3 Proposition (1.3.6)(ii), from closed normal
subgroups of profinite groups to arbitrary normal subgroups of compact topological
groups with jointly continuous discrete coefficients. -/
noncomputable def quotientCoind₁Iso [DiscreteTopology B] :
    quotientInvariants N (coind₁ B) ≅
      coind₁ (TopRep.of (ContRepresentation.trivial k (G ⧸ N) B)) := by
  letI : DiscreteTopology C(G, B) :=
    ContinuousMap.discreteTopology_of_compactSpace
  letI : DiscreteTopology C(G ⧸ N, B) :=
    ContinuousMap.discreteTopology_of_compactSpace
  refine ⟨ofHom {
    toContinuousLinearMap := {
      toFun := quotientCoind₁Forward N B
      map_add' := by
        intro f g
        change quotientInvariants N (coind₁ B) at f g
        ext q
        induction q using QuotientGroup.induction_on with
        | _ t =>
          change B.ρ t⁻¹ (f.1 t + g.1 t) =
            B.ρ t⁻¹ (f.1 t) + B.ρ t⁻¹ (g.1 t)
          simp
      map_smul' := by
        intro c f
        change quotientInvariants N (coind₁ B) at f
        ext q
        induction q using QuotientGroup.induction_on with
        | _ t =>
          change B.ρ t⁻¹ (c • f.1 t) = c • B.ρ t⁻¹ (f.1 t)
          simp
      cont := continuous_of_discreteTopology }
    isIntertwining' := by
      intro q
      induction q using QuotientGroup.induction_on with
      | _ g =>
        ext f x
        change quotientInvariants N (coind₁ B) at f
        induction x using QuotientGroup.induction_on with
        | _ t =>
          change B.ρ t⁻¹ (B.ρ g (f.1 (g⁻¹ * t))) =
            (ContRepresentation.trivial k (G ⧸ N) B)
              (QuotientGroup.mk' N g)
              ((quotientCoind₁Forward N B f)
                ((QuotientGroup.mk' N g)⁻¹ * QuotientGroup.mk' N t))
          rw [ContRepresentation.trivial_apply]
          have heq : (QuotientGroup.mk' N g)⁻¹ * QuotientGroup.mk' N t =
              QuotientGroup.mk' N (g⁻¹ * t) := by rw [map_mul, map_inv]
          rw [heq, quotientCoind₁Forward_apply_mk]
          change ((B.ρ t⁻¹) * (B.ρ g)) (f.1 (g⁻¹ * t)) =
            B.ρ (g⁻¹ * t)⁻¹ (f.1 (g⁻¹ * t))
          rw [← map_mul]
          congr 1
          group
  }, ofHom {
    toContinuousLinearMap := {
      toFun := quotientCoind₁Backward N B
      map_add' := by
        intro F H
        change C(G ⧸ N, B) at F H
        apply Subtype.ext
        ext t
        change B.ρ t ((F + H) (QuotientGroup.mk' N t)) =
          B.ρ t (F (QuotientGroup.mk' N t)) +
            B.ρ t (H (QuotientGroup.mk' N t))
        simp
      map_smul' := by
        intro c F
        change C(G ⧸ N, B) at F
        apply Subtype.ext
        ext t
        change B.ρ t ((c • F) (QuotientGroup.mk' N t)) =
          c • B.ρ t (F (QuotientGroup.mk' N t))
        simp
      cont := continuous_of_discreteTopology }
    isIntertwining' := by
      intro q
      induction q using QuotientGroup.induction_on with
      | _ g =>
        ext F t
        change B.ρ t
          (F ((QuotientGroup.mk' N g)⁻¹ * QuotientGroup.mk' N t)) =
          B.ρ g (B.ρ (g⁻¹ * t) (F (QuotientGroup.mk' N (g⁻¹ * t))))
        have heq : (QuotientGroup.mk' N g)⁻¹ * QuotientGroup.mk' N t =
            QuotientGroup.mk' N (g⁻¹ * t) := by rw [map_mul, map_inv]
        rw [heq]
        change B.ρ t (F (QuotientGroup.mk' N (g⁻¹ * t))) =
          ((B.ρ g) * (B.ρ (g⁻¹ * t)))
            (F (QuotientGroup.mk' N (g⁻¹ * t)))
        rw [← map_mul]
        congr 1
        group
  }, ?_, ?_⟩
  · apply hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    ext t
    change (quotientCoind₁Backward N B (quotientCoind₁Forward N B f)).1 t = f.1 t
    rw [quotientCoind₁Backward_apply, quotientCoind₁Forward_apply_mk]
    change ((B.ρ t) * (B.ρ t⁻¹)) (f.1 t) = f.1 t
    rw [← map_mul]
    simp
  · apply hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro F
    ext q
    induction q using QuotientGroup.induction_on with
    | _ t =>
      change quotientCoind₁Forward N B (quotientCoind₁Backward N B F)
        (QuotientGroup.mk' N t) = F (QuotientGroup.mk' N t)
      rw [quotientCoind₁Forward_apply_mk, quotientCoind₁Backward_apply]
      change ((B.ρ t⁻¹) * (B.ρ t)) (F (QuotientGroup.mk' N t)) =
        F (QuotientGroup.mk' N t)
      rw [← map_mul]
      simp

variable [DiscreteTopology B]

/-- Forward evaluation at a quotient coset untwists the coefficient action. -/
@[simp] theorem quotientCoind₁Iso_hom_apply_mk
    (f : quotientInvariants N (coind₁ B)) (t : G) :
    ((quotientCoind₁Iso N B).hom f) (QuotientGroup.mk' N t) =
      B.ρ t⁻¹ (f.1 t) := by
  change quotientCoind₁Forward N B f (QuotientGroup.mk' N t) = B.ρ t⁻¹ (f.1 t)
  exact quotientCoind₁Forward_apply_mk N B f t

/-- The inverse twists a quotient function by the original coefficient action. -/
@[simp] theorem quotientCoind₁Iso_inv_apply
    (F : coind₁ (TopRep.of (ContRepresentation.trivial k (G ⧸ N) B))) (t : G) :
    ((quotientCoind₁Iso N B).inv F).1 t =
      B.ρ t (F (QuotientGroup.mk' N t)) := by
  change (quotientCoind₁Backward N B F).1 t = B.ρ t (F (QuotientGroup.mk' N t))
  exact quotientCoind₁Backward_apply N B F t

/-- The forward and inverse formulas cancel on every quotient function. -/
theorem quotientCoind₁Iso_hom_inv_apply
    (F : coind₁ (TopRep.of (ContRepresentation.trivial k (G ⧸ N) B))) :
    (quotientCoind₁Iso N B).hom ((quotientCoind₁Iso N B).inv F) = F := by
  exact (quotientCoind₁Iso N B).inv_hom_id_apply F

/-- The forward and inverse formulas cancel on normal-invariant functions. -/
theorem quotientCoind₁Iso_inv_hom_apply
    (f : quotientInvariants N (coind₁ B)) :
    (quotientCoind₁Iso N B).inv ((quotientCoind₁Iso N B).hom f) = f := by
  exact (quotientCoind₁Iso N B).hom_inv_id_apply f

/-- The quotient action corresponds to translation of the quotient argument. -/
theorem quotientCoind₁Iso_hom_action
    (f : quotientInvariants N (coind₁ B)) (q : G ⧸ N) :
    (quotientCoind₁Iso N B).hom ((quotientInvariants N (coind₁ B)).ρ q f) =
      (coind₁ (TopRep.of (ContRepresentation.trivial k (G ⧸ N) B))).ρ q
        ((quotientCoind₁Iso N B).hom f) := by
  exact (quotientCoind₁Iso N B).hom.hom.isIntertwining q f

/-- The inverse respects the residual quotient action. -/
theorem quotientCoind₁Iso_inv_action
    (F : coind₁ (TopRep.of (ContRepresentation.trivial k (G ⧸ N) B))) (q : G ⧸ N) :
    (quotientCoind₁Iso N B).inv
        ((coind₁ (TopRep.of (ContRepresentation.trivial k (G ⧸ N) B))).ρ q F) =
      (quotientInvariants N (coind₁ B)).ρ q ((quotientCoind₁Iso N B).inv F) := by
  exact (quotientCoind₁Iso N B).inv.hom.isIntertwining q F

/-- The canonical equivalence commutes with equivariant coefficient maps. -/
theorem quotientCoind₁Iso_naturality {C : TopRep.{w} k G}
    [DiscreteTopology C] [JointlyContinuous C] (φ : B ⟶ C) :
    ((quotientInvariantsFunctor (k := k) N).map
      ((coind₁Functor k G).map φ)) ≫ (quotientCoind₁Iso N C).hom =
      (quotientCoind₁Iso N B).hom ≫
        ((coind₁Functor k (G ⧸ N)).map
          (trivialMap (H := G ⧸ N) φ.hom.toContinuousLinearMap)) := by
  ext f q
  induction q using QuotientGroup.induction_on with
  | _ t =>
    change quotientInvariants N (coind₁ B) at f
    change ((quotientCoind₁Iso N C).hom
      (quotientInvariantsMap N ((coind₁Functor k G).map φ) f))
        (QuotientGroup.mk' N t) =
      (((coind₁Functor k (G ⧸ N)).map
        (trivialMap (H := G ⧸ N) φ.hom.toContinuousLinearMap)).hom
        ((quotientCoind₁Iso N B).hom f)) (QuotientGroup.mk' N t)
    rw [quotientCoind₁Iso_hom_apply_mk]
    have hleft :
        (quotientInvariantsMap N ((coind₁Functor k G).map φ) f).1 t =
          φ.hom (f.1 t) := rfl
    have hright :
        (((coind₁Functor k (G ⧸ N)).map
          (trivialMap (H := G ⧸ N) φ.hom.toContinuousLinearMap)).hom
          ((quotientCoind₁Iso N B).hom f)) (QuotientGroup.mk' N t) =
            φ.hom (((quotientCoind₁Iso N B).hom f) (QuotientGroup.mk' N t)) := rfl
    rw [hleft, hright, quotientCoind₁Iso_hom_apply_mk]
    exact (φ.hom.isIntertwining t⁻¹ (f.1 t)).symm

end TopRep
