/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RepresentationTheory.Invariants

/-!
# Nested normal-subgroup invariants

This file supplies the coefficient bridge needed to compare finite quotient
cohomology through nested normal subgroups. If `S ≤ T` are normal subgroups of
`G` and `A` is a `G`-representation, taking `S`-invariants and then
`T / S`-invariants agrees with taking `T`-invariants directly.

The representation-level isomorphism records the third-isomorphism-theorem
identification `(G / S) / (T / S) ≃ G / T`; it is stronger than a bare
equivalence of the underlying modules and is intended for later deflation and
inflation constructions.
-/

public section

open CategoryTheory

namespace ContinuousGroupCohomology

universe u v w

variable {R : Type u} [CommRing R]
variable {G : Type v} [Group G]

/-- Taking invariants under `T / S` after taking invariants under `S` agrees
with taking invariants under `T`. -/
@[expose]
noncomputable def nestedQuotientInvariantsEquiv (A : Rep.{w} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) :
    Representation.invariants ((A.quotientToInvariants S).ρ.comp
      (T.map (QuotientGroup.mk' S)).subtype) ≃ₗ[R]
      Representation.invariants (A.ρ.comp T.subtype) where
  toFun x := ⟨x.1.1, by
    intro t
    let qt : T.map (QuotientGroup.mk' S) :=
      ⟨QuotientGroup.mk' S t.1, ⟨t.1, t.2, rfl⟩⟩
    exact congrArg Subtype.val (x.2 qt)⟩
  invFun y := ⟨⟨y.1, by
    intro s
    exact y.2 ⟨s.1, hST s.2⟩⟩, by
    intro q
    rcases q.2 with ⟨g, hg, hq⟩
    have hrep : (A.quotientToInvariants S).ρ q.1 =
        (A.quotientToInvariants S).ρ (QuotientGroup.mk' S g) :=
      congrArg (A.quotientToInvariants S).ρ hq.symm
    change (A.quotientToInvariants S).ρ q.1 _ = _
    rw [hrep]
    apply Subtype.ext
    exact y.2 ⟨g, hg⟩⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma nestedQuotientInvariantsEquiv_apply_val (A : Rep.{w} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    (x : Representation.invariants ((A.quotientToInvariants S).ρ.comp
      (T.map (QuotientGroup.mk' S)).subtype)) :
    (nestedQuotientInvariantsEquiv A S T hST x).1 = x.1.1 := rfl

@[simp]
lemma nestedQuotientInvariantsEquiv_symm_apply_val (A : Rep.{w} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    (x : Representation.invariants (A.ρ.comp T.subtype)) :
    ((nestedQuotientInvariantsEquiv A S T hST).symm x).1.1 = x.1 := rfl

/-- The nested-invariants equivalence is equivariant after the third
isomorphism theorem identifies the two quotient groups. -/
@[expose]
noncomputable def nestedQuotientInvariantsRepIso (A : Rep.{w} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) :
    (A.quotientToInvariants S).quotientToInvariants
        (T.map (QuotientGroup.mk' S)) ≅
      Rep.res (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom
        (A.quotientToInvariants T) :=
  Rep.mkIso <| Representation.Equiv.mk
    (nestedQuotientInvariantsEquiv A S T hST) fun q => by
      refine QuotientGroup.induction_on q ?_
      intro gS
      refine QuotientGroup.induction_on gS ?_
      intro g
      ext x
      rfl

@[simp]
lemma nestedQuotientInvariantsRepIso_hom_apply_val (A : Rep.{w} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    (x : (A.quotientToInvariants S).quotientToInvariants
      (T.map (QuotientGroup.mk' S))) :
    ((nestedQuotientInvariantsRepIso A S T hST).hom x).1 = x.1.1 := rfl

/-- The nested-invariants representation isomorphism is natural in the
coefficient representation. -/
@[reassoc]
lemma nestedQuotientInvariantsRepIso_naturality {A B : Rep.{w} R G}
    (f : A ⟶ B) (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) :
    (Rep.quotientToInvariantsFunctor R (T.map (QuotientGroup.mk' S))).map
        ((Rep.quotientToInvariantsFunctor R S).map f) ≫
      (nestedQuotientInvariantsRepIso B S T hST).hom =
    (nestedQuotientInvariantsRepIso A S T hST).hom ≫
      (Rep.resFunctor
        (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom).map
        ((Rep.quotientToInvariantsFunctor R T).map f) := by
  ext x
  rfl

/-- The natural transformation from iterated invariants to direct invariants,
after restriction along the third-isomorphism equivalence. -/
@[expose]
noncomputable def nestedQuotientInvariantsRepNatTrans
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) :
    Rep.quotientToInvariantsFunctor R S ⋙
        Rep.quotientToInvariantsFunctor R (T.map (QuotientGroup.mk' S)) ⟶
      Rep.quotientToInvariantsFunctor R T ⋙
        Rep.resFunctor
          (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom where
  app A := (nestedQuotientInvariantsRepIso A S T hST).hom
  naturality _ _ f := nestedQuotientInvariantsRepIso_naturality f S T hST

@[simp]
lemma nestedQuotientInvariantsRepNatTrans_app (A : Rep.{w} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) :
    (nestedQuotientInvariantsRepNatTrans S T hST).app A =
      (nestedQuotientInvariantsRepIso A S T hST).hom := rfl

end ContinuousGroupCohomology
