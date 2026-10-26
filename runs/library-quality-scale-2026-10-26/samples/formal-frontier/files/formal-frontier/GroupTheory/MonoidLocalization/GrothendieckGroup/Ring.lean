/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.MonoidLocalization.GrothendieckGroup
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Ring structures on additive Grothendieck groups

Multiplication in a non-unital, non-associative semiring extends in both variables to
its additive Grothendieck group as `Algebra.GrothendieckAddGroup.mulAddHom`. The
extension is characterized by its values on pairs of canonical generators. It is
associative, unital or commutative whenever the source multiplication has the
corresponding property.

For a semiring `A`, this gives a ring structure on the existing
`Algebra.GrothendieckAddGroup A`, retaining its additive group. A commutative semiring
gives a commutative ring with the same underlying ring. The canonical generator
`Algebra.GrothendieckAddGroup.ofRingHom` is a ring homomorphism whose entire underlying
additive homomorphism is the existing `Algebra.GrothendieckAddGroup.of`.

For any ring `S`, `Algebra.GrothendieckAddGroup.liftRingHom` extends a ring
homomorphism `A →+* S`, retaining its entire additive lift. The equivalence
`Algebra.GrothendieckAddGroup.liftRingEquiv` packages this universal property with
restriction along `ofRingHom` as its inverse. The source and target universes are
independent; neither commutativity nor nontriviality of the target is required.

## Implementation notes

Only semiring sources receive multiplication instances. The weaker multiplication
is available as a bundled biadditive map, without introducing additional weak ring
instances. Casts use the retained additive group's natural and integer scalar
operations on the generator of one. Multiplicativity of the ring-homomorphism lift
is proved by comparing biadditive maps on pairs of canonical generators.

## References

* Mathlib's Grothendieck completion and universal-property formalization by Alex J. Best
  and Yaël Dillies in `Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup`.
* The additive and biadditive Grothendieck lifts in
  `GroupTheory.MonoidLocalization.GrothendieckGroup`, including `hom_ext₂` for
  extensionality on pairs of generators.
* Mathlib's bundled multiplication API in `Mathlib.Algebra.Ring.Basic` by Jeremy Avigad,
  Leonardo de Moura, Floris van Doorn, Yury Kudryashov and Neil Strickland.
-/

@[expose] public section

universe u v

namespace Algebra.GrothendieckAddGroup

section Multiplication

variable {A : Type u} [NonUnitalNonAssocSemiring A]

/-- Multiplication extended additively in both variables to the additive completion. -/
noncomputable def mulAddHom :
    GrothendieckAddGroup A →+ GrothendieckAddGroup A →+ GrothendieckAddGroup A :=
  lift₂ ((AddMonoidHom.mul : A →+ A →+ A).compr₂ of)

/-- The extended multiplication agrees with multiplication on pairs of generators. -/
@[simp]
theorem mulAddHom_of (a b : A) : mulAddHom (of a) (of b) = of (a * b) := by
  exact lift₂_of ((AddMonoidHom.mul : A →+ A →+ A).compr₂ of) a b

/-- Generator values uniquely characterize the curried additive multiplication. -/
theorem mulAddHom_unique
    (f : GrothendieckAddGroup A →+ GrothendieckAddGroup A →+ GrothendieckAddGroup A)
    (h : ∀ a b : A, f (of a) (of b) = of (a * b)) : mulAddHom = f := by
  exact lift₂_unique ((AddMonoidHom.mul : A →+ A →+ A).compr₂ of) f h

/-- Equality with extended multiplication can be checked on pairs of generators. -/
theorem mulAddHom_eq_iff
    (f : GrothendieckAddGroup A →+ GrothendieckAddGroup A →+ GrothendieckAddGroup A) :
    mulAddHom = f ↔ ∀ a b : A, f (of a) (of b) = of (a * b) := by
  constructor
  · intro h a b
    rw [← h, mulAddHom_of]
  · exact mulAddHom_unique f

end Multiplication

/-- Associative multiplication on the source induces an associative biadditive extension. -/
theorem mulAddHom_assoc {A : Type u} [NonUnitalSemiring A]
    (x y z : GrothendieckAddGroup A) :
    mulAddHom (mulAddHom x y) z = mulAddHom x (mulAddHom y z) := by
  let G := GrothendieckAddGroup A
  let μ : G →+ G →+ G := mulAddHom (A := A)
  have h :
      (μ.compr₂ μ : G →+ G →+ G →+ G) =
        ((AddMonoidHom.compHom.comp μ).compl₂ μ : G →+ G →+ G →+ G) := by
    apply hom_ext (A := A) (G := G →+ G →+ G)
    intro a
    apply hom_ext (A := A) (G := G →+ G)
    intro b
    apply hom_ext (A := A) (G := G)
    intro c
    change mulAddHom (mulAddHom (of a) (of b)) (of c) =
      mulAddHom (of a) (mulAddHom (of b) (of c))
    simp only [mulAddHom_of, mul_assoc]
  exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun h x) y) z

/-- The generator of one is a left identity for the extended multiplication. -/
theorem one_mulAddHom {A : Type u} [NonAssocSemiring A] (x : GrothendieckAddGroup A) :
    mulAddHom (of 1) x = x := by
  have h : mulAddHom (of (M := A) 1) = AddMonoidHom.id (GrothendieckAddGroup A) := by
    apply hom_ext
    intro a
    simp only [mulAddHom_of, one_mul, AddMonoidHom.id_apply]
  exact DFunLike.congr_fun h x

/-- The generator of one is a right identity for the extended multiplication. -/
theorem mulAddHom_one {A : Type u} [NonAssocSemiring A] (x : GrothendieckAddGroup A) :
    mulAddHom x (of 1) = x := by
  have h : (mulAddHom (A := A)).flip (of 1) =
      AddMonoidHom.id (GrothendieckAddGroup A) := by
    apply hom_ext
    intro a
    simp only [AddMonoidHom.flip_apply, mulAddHom_of, mul_one, AddMonoidHom.id_apply]
  exact DFunLike.congr_fun h x

/-- Commutativity of the source multiplication extends to the additive completion. -/
theorem mulAddHom_comm {A : Type u} [NonUnitalNonAssocSemiring A] [IsMulCommutative A]
    (x y : GrothendieckAddGroup A) : mulAddHom x y = mulAddHom y x := by
  have h : mulAddHom (A := A) = (mulAddHom (A := A)).flip := by
    apply hom_ext₂
    intro a b
    simp only [AddMonoidHom.flip_apply, mulAddHom_of]
    exact congrArg (of (M := A)) (mul_comm' a b)
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

-- Retain the additive structures and bundled maps before registering ring instances.
private def additiveGroup (A : Type u) [AddCommMonoid A] :
    AddCommGroup (GrothendieckAddGroup A) := inferInstance

private def additiveGenerator (A : Type u) [AddCommMonoid A] :
    A →+ GrothendieckAddGroup A := of

private noncomputable def biadditiveMultiplication (A : Type u)
    [NonUnitalNonAssocSemiring A] :
    GrothendieckAddGroup A →+ GrothendieckAddGroup A →+ GrothendieckAddGroup A := mulAddHom

private noncomputable def additiveLift (A : Type u) (G : Type v)
    [AddCommMonoid A] [AddCommGroup G] :
    (A →+ G) ≃ (GrothendieckAddGroup A →+ G) := lift

private noncomputable def additiveLiftEquiv (A : Type u) (G : Type v)
    [AddCommMonoid A] [AddCommGroup G] :
    (A →+ G) ≃+ (GrothendieckAddGroup A →+ G) := liftAddEquiv

/-- The ring structure induced by a semiring on its additive Grothendieck group. -/
noncomputable instance instRing (A : Type u) [Semiring A] :
    Ring (GrothendieckAddGroup A) :=
  let addGroup : AddCommGroup (GrothendieckAddGroup A) := inferInstance
  let generator : A →+ GrothendieckAddGroup A := of
  let μ : GrothendieckAddGroup A →+ GrothendieckAddGroup A →+
      GrothendieckAddGroup A := mulAddHom
  { addGroup with
    mul := fun x y => μ x y
    one := generator 1
    natCast := fun n => addGroup.nsmul n (generator 1)
    natCast_zero := addGroup.nsmul_zero (generator 1)
    natCast_succ := fun n => addGroup.nsmul_succ n (generator 1)
    intCast := fun z => addGroup.zsmul z (generator 1)
    intCast_ofNat := fun n => natCast_zsmul (generator 1) n
    intCast_negSucc := fun n => negSucc_zsmul (generator 1) n
    mul_assoc := mulAddHom_assoc
    one_mul := one_mulAddHom
    mul_one := mulAddHom_one
    left_distrib := fun x y z => (μ x).map_add y z
    right_distrib := fun x y z => (μ.flip z).map_add x y
    mul_zero := fun x => (μ x).map_zero
    zero_mul := fun x => (μ.flip x).map_zero }

/-- The commutative ring structure induced by a commutative semiring. -/
noncomputable instance instCommRing (A : Type u) [CommSemiring A] :
    CommRing (GrothendieckAddGroup A) :=
  { instRing A with mul_comm := mulAddHom_comm }

/-- Multiplication in the induced ring is the biadditive extension. -/
theorem mul_eq_mulAddHom {A : Type u} [Semiring A] (x y : GrothendieckAddGroup A) :
    x * y = mulAddHom x y := rfl

/-- The unit is the canonical generator of one. This is an explicit representation formula. -/
theorem one_def {A : Type u} [Semiring A] :
    (1 : GrothendieckAddGroup A) = of (M := A) 1 := rfl

/-- Natural casts use the retained additive group's natural scalar operation. -/
theorem natCast_def {A : Type u} [Semiring A] (n : ℕ) :
    (n : GrothendieckAddGroup A) = n • of (M := A) 1 := rfl

/-- Integer casts use the retained additive group's integer scalar operation. -/
theorem intCast_def {A : Type u} [Semiring A] (z : ℤ) :
    (z : GrothendieckAddGroup A) = z • of (M := A) 1 := rfl

/-- The canonical generator preserves one. -/
@[simp]
theorem of_one {A : Type u} [Semiring A] : of (M := A) 1 = 1 := rfl

/-- The canonical generator preserves multiplication. -/
theorem of_mul {A : Type u} [Semiring A] (a b : A) :
    of (a * b) = of a * of b := (mulAddHom_of a b).symm

/-- The canonical generator preserves natural casts. -/
@[simp]
theorem of_natCast {A : Type u} [Semiring A] (n : ℕ) :
    of (M := A) (n : A) = (n : GrothendieckAddGroup A) := by
  change of (M := A) (n : A) = n • of (M := A) 1
  exact (congrArg (of (M := A)) (nsmul_one n)).symm.trans
    (map_nsmul (of (M := A)) n (1 : A))

/-- The canonical map from a semiring to the ring on its additive Grothendieck group. -/
noncomputable def ofRingHom (A : Type u) [Semiring A] : A →+* GrothendieckAddGroup A :=
  { of (M := A) with
    map_one' := rfl
    map_mul' := fun a b => (mulAddHom_of a b).symm }

/-- The canonical ring homomorphism retains the entire additive generator. -/
@[simp]
theorem ofRingHom_toAddMonoidHom (A : Type u) [Semiring A] :
    (ofRingHom A).toAddMonoidHom = of (M := A) := rfl

/-- The canonical ring homomorphism evaluates as the additive generator. -/
@[simp]
theorem ofRingHom_apply {A : Type u} [Semiring A] (a : A) :
    ofRingHom A a = of a := rfl

-- Whole structures and bundled maps, not only their pointwise operations, are retained.
private theorem instRing_preserves (A : Type u) [Semiring A] :
    (instRing A).toAddCommGroup = additiveGroup A ∧
      (instRing A).natCast = (fun n => (additiveGroup A).nsmul n (additiveGenerator A 1)) ∧
      (instRing A).intCast = (fun z => (additiveGroup A).zsmul z (additiveGenerator A 1)) ∧
      (inferInstance : AddCommGroup (GrothendieckAddGroup A)) = additiveGroup A ∧
      (of : A →+ GrothendieckAddGroup A) = additiveGenerator A ∧
      (ofRingHom A).toAddMonoidHom = additiveGenerator A ∧
      (mulAddHom : GrothendieckAddGroup A →+ GrothendieckAddGroup A →+
        GrothendieckAddGroup A) = biadditiveMultiplication A ∧
      (AddMonoidHom.mul : GrothendieckAddGroup A →+ GrothendieckAddGroup A →+
        GrothendieckAddGroup A) = biadditiveMultiplication A := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem instRing_preserves_lifts (A : Type u) (G : Type v)
    [Semiring A] [AddCommGroup G] :
    (lift (M := A) (G := G)) = additiveLift A G ∧
      (liftAddEquiv (A := A) (G := G)) = additiveLiftEquiv A G := by
  exact ⟨rfl, rfl⟩

private theorem instCommRing_preserves (A : Type u) [CommSemiring A] :
    (instCommRing A).toRing = instRing A ∧
      (instCommRing A).toCommMonoid.toMonoid = (instRing A).toSemiring.toMonoid ∧
      (inferInstance : Ring (GrothendieckAddGroup A)) = instRing A ∧
      (inferInstance : CommSemiring (GrothendieckAddGroup A)).toSemiring =
        (instRing A).toSemiring ∧
      (inferInstance : AddCommGroup (GrothendieckAddGroup A)) = additiveGroup A ∧
      (of : A →+ GrothendieckAddGroup A) = additiveGenerator A ∧
      (ofRingHom A).toAddMonoidHom = additiveGenerator A ∧
      (mulAddHom : GrothendieckAddGroup A →+ GrothendieckAddGroup A →+
        GrothendieckAddGroup A) = biadditiveMultiplication A ∧
      (AddMonoidHom.mul : GrothendieckAddGroup A →+ GrothendieckAddGroup A →+
        GrothendieckAddGroup A) = biadditiveMultiplication A := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

section RingLifts

variable {A : Type u} {S : Type v} [Semiring A] [Ring S]

/-- Extend a ring homomorphism to the additive Grothendieck group, retaining its
additive lift. -/
noncomputable def liftRingHom (f : A →+* S) : GrothendieckAddGroup A →+* S :=
  { lift f.toAddMonoidHom with
    map_one' := by
      change lift f.toAddMonoidHom (of (1 : A)) = (1 : S)
      exact (lift_of f.toAddMonoidHom (1 : A)).trans f.map_one
    map_mul' := by
      apply (AddMonoidHom.map_mul_iff (lift f.toAddMonoidHom)).mpr
      apply hom_ext₂
      intro a b
      change lift f.toAddMonoidHom (mulAddHom (of a) (of b)) =
        lift f.toAddMonoidHom (of a) * lift f.toAddMonoidHom (of b)
      simp only [mulAddHom_of, lift_of]
      exact f.map_mul a b }

/-- The entire underlying additive homomorphism is the Grothendieck additive lift. -/
@[simp]
theorem liftRingHom_toAddMonoidHom (f : A →+* S) :
    (liftRingHom f).toAddMonoidHom = lift f.toAddMonoidHom := rfl

/-- The ring lift evaluates as the additive lift. -/
theorem liftRingHom_apply (f : A →+* S) (x : GrothendieckAddGroup A) :
    liftRingHom f x = lift f.toAddMonoidHom x := rfl

/-- The ring lift agrees with the supplied homomorphism on canonical generators. -/
@[simp]
theorem liftRingHom_of (f : A →+* S) (a : A) : liftRingHom f (of a) = f a := by
  exact lift_of f.toAddMonoidHom a

/-- Ring homomorphisms out of the completion are determined by canonical generators. -/
@[ext]
theorem ringHom_ext {F G : GrothendieckAddGroup A →+* S}
    (h : ∀ a : A, F (of a) = G (of a)) : F = G := by
  apply RingHom.coe_addMonoidHom_injective
  exact hom_ext h

/-- The ring lift is the unique ring homomorphism with the prescribed generator values. -/
theorem liftRingHom_unique (f : A →+* S) (F : GrothendieckAddGroup A →+* S)
    (h : ∀ a : A, F (of a) = f a) : liftRingHom f = F := by
  apply ringHom_ext
  intro a
  exact (liftRingHom_of f a).trans (h a).symm

/-- The ring-homomorphism universal property of the additive Grothendieck group,
with restriction along `ofRingHom` as its inverse. -/
noncomputable def liftRingEquiv : (A →+* S) ≃ (GrothendieckAddGroup A →+* S) where
  toFun := liftRingHom
  invFun F := F.comp (ofRingHom A)
  left_inv f := by
    apply RingHom.ext
    intro a
    exact liftRingHom_of f a
  right_inv F := by
    apply ringHom_ext
    intro a
    exact liftRingHom_of (F.comp (ofRingHom A)) a

/-- The entire forward function of the universal-property equivalence is the ring lift. -/
@[simp]
theorem liftRingEquiv_toFun :
    (liftRingEquiv (A := A) (S := S)).toFun = liftRingHom := rfl

/-- The entire inverse function is restriction along the canonical ring homomorphism. -/
@[simp]
theorem liftRingEquiv_invFun :
    (liftRingEquiv (A := A) (S := S)).invFun =
      (fun F => F.comp (ofRingHom A)) := rfl

/-- The universal-property equivalence evaluates as the canonical ring lift. -/
@[simp]
theorem liftRingEquiv_apply (f : A →+* S) : liftRingEquiv f = liftRingHom f := rfl

/-- The inverse equivalence restricts along the canonical ring homomorphism. -/
@[simp]
theorem liftRingEquiv_symm_apply (F : GrothendieckAddGroup A →+* S) :
    (liftRingEquiv (A := A) (S := S)).symm F = F.comp (ofRingHom A) := rfl

end RingLifts

end Algebra.GrothendieckAddGroup
