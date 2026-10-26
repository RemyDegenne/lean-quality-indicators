/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Category.FiniteProjective
public import ProjectiveModules.Module.RightExtension
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.LinearAlgebra.Pi

/-!
# Right modules over products of coefficient rings

A family of right modules over a family of semirings has an ordinary function
carrier and a coordinatewise action of the opposite of the coefficient product.
`Module.piRightModule` specifies this action using Mathlib's coefficient-family
Pi module, the opposite-product ring equivalence, and scalar pullback.
`Module.prodRightModule` gives the independently sized binary construction.
Neither construction is a global scalar-action instance.

At Ring scope, `ModuleCat.piRight` and `ModuleCat.prodRight` bundle the same data.
`ModuleCat.FiniteProjective.pi` and `ModuleCat.FiniteProjective.prodRight` assemble
finite-projective factors without assuming projectivity of the output. The Pi
assembly requires a finite index; the module data itself does not.
The right-extension comparisons use the existing balanced-tensor objects along
coordinate projections, rather than a replacement extension construction.

## Implementation notes

The index, coefficient and carrier universes are independent. Binary coefficient
rings and binary module carriers each have independent universes. Coordinate
inclusions are supported functions, not unital homomorphisms into the product.
Evaluation is semilinear along the opposite of the coordinate projection.
No generic restriction-projectivity result or categorical equivalence is used.

## References

The constructions reuse Mathlib's Pi and product module structures, opposite ring
equivalence, scalar pullback, and supported-function data, together with the
finite-projective and right scalar-extension interfaces of Projective Modules.
The projectivity arguments use Mathlib's Finsupp-section description of projective
modules. Coordinate reconstruction uses the universal property of the balanced
tensor product and the supported coordinate idempotents.
-/

@[expose] public section

universe uι uR uS uM uN

namespace Module

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) (Mi : ι → Type uM)
variable [∀ i, Semiring (Ri i)] [∀ i, AddCommMonoid (Mi i)]
variable [∀ i, Module (Ri i)ᵐᵒᵖ (Mi i)]

/-- The coordinatewise right action of a coefficient product on a function
family. The underlying carrier is the ordinary dependent function type. -/
@[instance_reducible]
def piRightModule : Module (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i) :=
  letI : Module (∀ i, (Ri i)ᵐᵒᵖ) (∀ i, Mi i) := Pi.module'
  Module.compHom (∀ i, Mi i) (RingEquiv.piMulOpposite Ri).toRingHom

/-- A product scalar acts through its corresponding coordinate. -/
theorem piRightModule_smul_apply (a : ∀ i, Ri i) (x : ∀ i, Mi i) (i : ι) :
    (@SMul.smul _ _ (piRightModule Ri Mi).toSMul (MulOpposite.op a) x) i =
      MulOpposite.op (a i) • x i := by
  rfl

/-- Coordinate evaluation for the right coefficient-product action is
semilinear along the opposite coordinate projection. -/
def piRightEval (i : ι) :
    @LinearMap (∀ j, Ri j)ᵐᵒᵖ (Ri i)ᵐᵒᵖ _ _
      (RingHom.op (Pi.evalRingHom Ri i)) (∀ j, Mi j) (Mi i) _ _
      (piRightModule Ri Mi) inferInstance :=
  letI : Module (∀ j, Ri j)ᵐᵒᵖ (∀ j, Mi j) := piRightModule Ri Mi
  { toFun := fun x => x i
    map_add' := by
      intro x y
      rfl
    map_smul' := by
      intro a x
      exact piRightModule_smul_apply Ri Mi a.unop x i }

/-- The semilinear coordinate map is ordinary function evaluation. -/
theorem piRightEval_apply (i : ι) (x : ∀ j, Mi j) :
    piRightEval Ri Mi i x = x i := by
  rfl

/-- Finite families of finitely generated factor modules are finitely generated
for the canonical right coefficient-product action. -/
theorem finite_piRight [Finite ι] [∀ i, Module.Finite (Ri i)ᵐᵒᵖ (Mi i)] :
    @Module.Finite (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i) _ _ (piRightModule Ri Mi) := by
  classical
  let f (i : ι) : (∀ j, Ri j)ᵐᵒᵖ →+* (Ri i)ᵐᵒᵖ :=
    RingHom.op (Pi.evalRingHom Ri i)
  let : ∀ i, Module (∀ j, Ri j)ᵐᵒᵖ (Mi i) := fun i => Module.compHom (Mi i) (f i)
  have : ∀ i, Module.Finite (∀ j, Ri j)ᵐᵒᵖ (Mi i) := fun i => by
    let : Module (∀ j, Ri j)ᵐᵒᵖ (Ri i)ᵐᵒᵖ := Module.compHom (Ri i)ᵐᵒᵖ (f i)
    let : IsScalarTower (∀ j, Ri j)ᵐᵒᵖ (Ri i)ᵐᵒᵖ (Mi i) :=
      SMul.comp.isScalarTower (f i)
    have : Module.Finite (∀ j, Ri j)ᵐᵒᵖ (Ri i)ᵐᵒᵖ := by
      refine Module.Finite.of_surjective (Module.compHom.toLinearMap (f i)) ?_
      intro r
      refine ⟨MulOpposite.op (Pi.single i r.unop), ?_⟩
      change MulOpposite.op ((Pi.single i r.unop) i) = r
      simp only [Pi.single_eq_same, MulOpposite.op_unop]
    exact Module.Finite.trans (Ri i)ᵐᵒᵖ (Mi i)
  exact inferInstanceAs (Module.Finite (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i))

/-- Finite families of projective factor modules are projective for the
canonical right coefficient-product action. -/
theorem projective_piRight [Finite ι] [∀ i, Module.Projective (Ri i)ᵐᵒᵖ (Mi i)] :
    @Module.Projective (∀ i, Ri i)ᵐᵒᵖ _ (∀ i, Mi i) _ (piRightModule Ri Mi) := by
  classical
  let A := (∀ i, Ri i)ᵐᵒᵖ
  let φ : ∀ i, A →+* (Ri i)ᵐᵒᵖ := fun i => RingHom.op (Pi.evalRingHom Ri i)
  let : ∀ i, Module A (Ri i)ᵐᵒᵖ := fun i => Module.compHom _ (φ i)
  let : ∀ i, Module A (Mi i) := fun i => Module.compHom _ (φ i)
  let : ∀ i, Module.Projective A (Mi i) := fun i => by
    -- The supported coefficient section is linear, not a unital ring map.
    let σ : (Ri i)ᵐᵒᵖ →ₗ[A] A :=
      { toFun := fun r => MulOpposite.op (Pi.single i r.unop)
        map_add' := by
          intro r s
          apply MulOpposite.unop_injective
          funext j
          change Pi.single i (r.unop + s.unop) j =
            Pi.single i r.unop j + Pi.single i s.unop j
          by_cases h : j = i
          · subst j
            simp
          · simp [Pi.single_eq_of_ne h]
        map_smul' := by
          intro a r
          apply MulOpposite.unop_injective
          funext j
          change Pi.single i (r.unop * a.unop i) j =
            Pi.single i r.unop j * a.unop j
          by_cases h : j = i
          · subst j
            simp
          · simp [Pi.single_eq_of_ne h] }
    have hσ (r : (Ri i)ᵐᵒᵖ) : φ i (σ r) = r := by
      apply MulOpposite.unop_injective
      change Pi.single i r.unop i = r.unop
      exact Pi.single_eq_same i r.unop
    obtain ⟨s, hs⟩ := (inferInstance : Module.Projective (Ri i)ᵐᵒᵖ (Mi i)).out
    let sA : Mi i →ₗ[A] (Mi i →₀ (Ri i)ᵐᵒᵖ) :=
      { toFun := s
        map_add' := s.map_add
        map_smul' := by
          intro a x
          change s (φ i a • x) = φ i a • s x
          exact s.map_smul (φ i a) x }
    refine ⟨⟨(Finsupp.mapRange.linearMap σ).comp sA, ?_⟩⟩
    intro x
    change Finsupp.linearCombination A id ((s x).mapRange σ σ.map_zero) = x
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (f := σ) (g := s x) (h := fun m a => a • id m)
        (fun m => zero_smul A (id m))]
    change (s x).sum (fun m r => φ i (σ r) • m) = x
    simp only [hσ]
    exact hs x
  let := Fintype.ofFinite ι
  have hmod : piRightModule Ri Mi = Pi.module ι Mi A := by
    apply Module.ext'
    intro a x
    funext i
    exact piRightModule_smul_apply Ri Mi a.unop x i
  rw [hmod]
  exact Module.Projective.of_equiv'
    (DFinsupp.linearEquivFunOnFintype (R := A) (M := Mi))

variable (Ni : ι → Type uN) [∀ i, AddCommMonoid (Ni i)]
variable [∀ i, Module (Ri i)ᵐᵒᵖ (Ni i)]

/-- Factorwise right-linear equivalences assemble to an equivalence for the
canonical product action, in independent carrier universes. -/
def piRightCongr (e : ∀ i, Mi i ≃ₗ[(Ri i)ᵐᵒᵖ] Ni i) :
    @LinearEquiv (∀ i, Ri i)ᵐᵒᵖ (∀ i, Ri i)ᵐᵒᵖ _ _
      (RingHom.id _) (RingHom.id _) _ _ (∀ i, Mi i) (∀ i, Ni i) _ _
      (piRightModule Ri Mi) (piRightModule Ri Ni) :=
  letI : Module (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i) := piRightModule Ri Mi
  letI : Module (∀ i, Ri i)ᵐᵒᵖ (∀ i, Ni i) := piRightModule Ri Ni
  { __ := AddEquiv.piCongrRight (fun i => (e i).toAddEquiv)
    map_smul' := by
      intro a x
      funext i
      change e i ((MulOpposite.op a.unop • x) i) =
        (MulOpposite.op a.unop • (fun j => e j (x j))) i
      calc
        e i ((MulOpposite.op a.unop • x) i) =
            e i (MulOpposite.op (a.unop i) • x i) :=
          congrArg (e i) (piRightModule_smul_apply Ri Mi a.unop x i)
        _ = MulOpposite.op (a.unop i) • e i (x i) := (e i).map_smul _ _
        _ = (MulOpposite.op a.unop • (fun j => e j (x j))) i :=
          (piRightModule_smul_apply Ri Ni a.unop (fun j => e j (x j)) i).symm }

/-- The assembled equivalence acts coordinatewise. -/
theorem piRightCongr_apply (e : ∀ i, Mi i ≃ₗ[(Ri i)ᵐᵒᵖ] Ni i)
    (x : ∀ i, Mi i) (i : ι) : piRightCongr Ri Mi Ni e x i = e i (x i) := by
  rfl

/-- The inverse assembled equivalence acts coordinatewise. -/
theorem piRightCongr_symm_apply (e : ∀ i, Mi i ≃ₗ[(Ri i)ᵐᵒᵖ] Ni i)
    (x : ∀ i, Ni i) (i : ι) :
    (piRightCongr Ri Mi Ni e).symm x i = (e i).symm (x i) := by
  rfl

/-- Coordinatewise binary direct sum commutes with coefficient-product assembly.
The right-hand product uses Mathlib's same-scalar product module. -/
def piRightProdLinearEquiv :
    @LinearEquiv (∀ i, Ri i)ᵐᵒᵖ (∀ i, Ri i)ᵐᵒᵖ _ _
      (RingHom.id _) (RingHom.id _) _ _
      (∀ i, Mi i × Ni i) ((∀ i, Mi i) × (∀ i, Ni i)) _ _
      (piRightModule Ri (fun i => Mi i × Ni i))
      (@Prod.instModule (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i) (∀ i, Ni i) _ _ _
        (piRightModule Ri Mi) (piRightModule Ri Ni)) :=
  letI : Module (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i) := piRightModule Ri Mi
  letI : Module (∀ i, Ri i)ᵐᵒᵖ (∀ i, Ni i) := piRightModule Ri Ni
  letI : Module (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i × Ni i) :=
    piRightModule Ri (fun i => Mi i × Ni i)
  { __ := Equiv.arrowProdEquivProdArrow ι Mi Ni
    map_add' := by
      intro x y
      rfl
    map_smul' := by
      intro a x
      apply Prod.ext
      · funext i
        change ((MulOpposite.op a.unop • x) i).1 =
          (MulOpposite.op a.unop • (fun j => (x j).1)) i
        calc
          ((MulOpposite.op a.unop • x) i).1 =
              (MulOpposite.op (a.unop i) • x i).1 :=
            congrArg Prod.fst
              (piRightModule_smul_apply Ri (fun j => Mi j × Ni j) a.unop x i)
          _ = MulOpposite.op (a.unop i) • (x i).1 := rfl
          _ = (MulOpposite.op a.unop • (fun j => (x j).1)) i :=
            (piRightModule_smul_apply Ri Mi a.unop (fun j => (x j).1) i).symm
      · funext i
        change ((MulOpposite.op a.unop • x) i).2 =
          (MulOpposite.op a.unop • (fun j => (x j).2)) i
        calc
          ((MulOpposite.op a.unop • x) i).2 =
              (MulOpposite.op (a.unop i) • x i).2 :=
            congrArg Prod.snd
              (piRightModule_smul_apply Ri (fun j => Mi j × Ni j) a.unop x i)
          _ = MulOpposite.op (a.unop i) • (x i).2 := rfl
          _ = (MulOpposite.op a.unop • (fun j => (x j).2)) i :=
            (piRightModule_smul_apply Ri Ni a.unop (fun j => (x j).2) i).symm }

/-- Direct-sum rearrangement separates the two coordinate families. -/
theorem piRightProdLinearEquiv_apply (x : ∀ i, Mi i × Ni i) :
    piRightProdLinearEquiv Ri Mi Ni x =
      (fun i => (x i).1, fun i => (x i).2) := by
  rfl

/-- The inverse direct-sum rearrangement pairs the coordinate families. -/
theorem piRightProdLinearEquiv_symm_apply (x : (∀ i, Mi i) × (∀ i, Ni i)) :
    (piRightProdLinearEquiv Ri Mi Ni).symm x = fun i => (x.1 i, x.2 i) := by
  rfl

end Pi

section Prod

variable (R : Type uR) (S : Type uS) (M : Type uM) (N : Type uN)
variable [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
variable [Module Rᵐᵒᵖ M] [Module Sᵐᵒᵖ N]

/-- The right action of two independently sized coefficient rings on a binary
module product, obtained from the genuine projections and the same-scalar
product module. -/
@[instance_reducible]
def prodRightModule : Module (R × S)ᵐᵒᵖ (M × N) :=
  letI : Module (R × S)ᵐᵒᵖ M := Module.compHom M (RingHom.op (RingHom.fst R S))
  letI : Module (R × S)ᵐᵒᵖ N := Module.compHom N (RingHom.op (RingHom.snd R S))
  Prod.instModule

/-- The heterogeneous binary action is coordinatewise right multiplication. -/
theorem prodRightModule_smul (r : R) (s : S) (m : M) (n : N) :
    @SMul.smul _ _ (prodRightModule R S M N).toSMul (MulOpposite.op (r, s)) (m, n) =
      (MulOpposite.op r • m, MulOpposite.op s • n) := by
  rfl

/-- Finitely generated right factor modules have a finitely generated binary
product over the product coefficient semiring. -/
theorem finite_prodRight [Module.Finite Rᵐᵒᵖ M] [Module.Finite Sᵐᵒᵖ N] :
    @Module.Finite (R × S)ᵐᵒᵖ (M × N) _ _ (prodRightModule R S M N) := by
  let f : (R × S)ᵐᵒᵖ →+* Rᵐᵒᵖ := RingHom.op (RingHom.fst R S)
  let g : (R × S)ᵐᵒᵖ →+* Sᵐᵒᵖ := RingHom.op (RingHom.snd R S)
  let : Module (R × S)ᵐᵒᵖ M := Module.compHom M f
  let : Module (R × S)ᵐᵒᵖ N := Module.compHom N g
  have : Module.Finite (R × S)ᵐᵒᵖ M := by
    let : Module (R × S)ᵐᵒᵖ Rᵐᵒᵖ := Module.compHom Rᵐᵒᵖ f
    let : IsScalarTower (R × S)ᵐᵒᵖ Rᵐᵒᵖ M := SMul.comp.isScalarTower f
    have : Module.Finite (R × S)ᵐᵒᵖ Rᵐᵒᵖ := by
      refine Module.Finite.of_surjective (Module.compHom.toLinearMap f) ?_
      intro r
      refine ⟨MulOpposite.op (r.unop, 0), ?_⟩
      change MulOpposite.op r.unop = r
      exact MulOpposite.op_unop r
    exact Module.Finite.trans Rᵐᵒᵖ M
  have : Module.Finite (R × S)ᵐᵒᵖ N := by
    let : Module (R × S)ᵐᵒᵖ Sᵐᵒᵖ := Module.compHom Sᵐᵒᵖ g
    let : IsScalarTower (R × S)ᵐᵒᵖ Sᵐᵒᵖ N := SMul.comp.isScalarTower g
    have : Module.Finite (R × S)ᵐᵒᵖ Sᵐᵒᵖ := by
      refine Module.Finite.of_surjective (Module.compHom.toLinearMap g) ?_
      intro s
      refine ⟨MulOpposite.op (0, s.unop), ?_⟩
      change MulOpposite.op s.unop = s
      exact MulOpposite.op_unop s
    exact Module.Finite.trans Sᵐᵒᵖ N
  exact inferInstanceAs (Module.Finite (R × S)ᵐᵒᵖ (M × N))

/-- Projective right factor modules have a projective binary product over the
product coefficient semiring. -/
theorem projective_prodRight [Module.Projective Rᵐᵒᵖ M] [Module.Projective Sᵐᵒᵖ N] :
    @Module.Projective (R × S)ᵐᵒᵖ _ (M × N) _ (prodRightModule R S M N) := by
  let A := (R × S)ᵐᵒᵖ
  let φR : A →+* Rᵐᵒᵖ := RingHom.op (RingHom.fst R S)
  let φS : A →+* Sᵐᵒᵖ := RingHom.op (RingHom.snd R S)
  let : Module A Rᵐᵒᵖ := Module.compHom _ φR
  let : Module A Sᵐᵒᵖ := Module.compHom _ φS
  let : Module A M := Module.compHom _ φR
  let : Module A N := Module.compHom _ φS
  let σR : Rᵐᵒᵖ →ₗ[A] A :=
    { toFun := fun r => MulOpposite.op (r.unop, 0)
      map_add' := by
        intro r s
        apply MulOpposite.unop_injective
        change (r.unop + s.unop, (0 : S)) = (r.unop, 0) + (s.unop, 0)
        simp
      map_smul' := by
        intro a r
        apply MulOpposite.unop_injective
        change (r.unop * a.unop.1, (0 : S)) = (r.unop, 0) * a.unop
        apply Prod.ext
        · rfl
        · exact (zero_mul a.unop.2).symm }
  let σS : Sᵐᵒᵖ →ₗ[A] A :=
    { toFun := fun s => MulOpposite.op (0, s.unop)
      map_add' := by
        intro r s
        apply MulOpposite.unop_injective
        change ((0 : R), r.unop + s.unop) = (0, r.unop) + (0, s.unop)
        simp
      map_smul' := by
        intro a s
        apply MulOpposite.unop_injective
        change ((0 : R), s.unop * a.unop.2) = (0, s.unop) * a.unop
        apply Prod.ext
        · exact (zero_mul a.unop.1).symm
        · rfl }
  have hσR (r : Rᵐᵒᵖ) : φR (σR r) = r := by
    apply MulOpposite.unop_injective
    rfl
  have hσS (s : Sᵐᵒᵖ) : φS (σS s) = s := by
    apply MulOpposite.unop_injective
    rfl
  let : Module.Projective A M := by
    obtain ⟨s, hs⟩ := (inferInstance : Module.Projective Rᵐᵒᵖ M).out
    let sA : M →ₗ[A] (M →₀ Rᵐᵒᵖ) :=
      { toFun := s
        map_add' := s.map_add
        map_smul' := by
          intro a x
          change s (φR a • x) = φR a • s x
          exact s.map_smul (φR a) x }
    refine ⟨⟨(Finsupp.mapRange.linearMap σR).comp sA, ?_⟩⟩
    intro x
    change Finsupp.linearCombination A id ((s x).mapRange σR σR.map_zero) = x
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (f := σR) (g := s x) (h := fun m a => a • id m)
        (fun m => zero_smul A (id m))]
    change (s x).sum (fun m r => φR (σR r) • m) = x
    simp only [hσR]
    exact hs x
  let : Module.Projective A N := by
    obtain ⟨s, hs⟩ := (inferInstance : Module.Projective Sᵐᵒᵖ N).out
    let sA : N →ₗ[A] (N →₀ Sᵐᵒᵖ) :=
      { toFun := s
        map_add' := s.map_add
        map_smul' := by
          intro a x
          change s (φS a • x) = φS a • s x
          exact s.map_smul (φS a) x }
    refine ⟨⟨(Finsupp.mapRange.linearMap σS).comp sA, ?_⟩⟩
    intro x
    change Finsupp.linearCombination A id ((s x).mapRange σS σS.map_zero) = x
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (f := σS) (g := s x) (h := fun n a => a • id n)
        (fun n => zero_smul A (id n))]
    change (s x).sum (fun n r => φS (σS r) • n) = x
    simp only [hσS]
    exact hs x
  change Module.Projective A (M × N)
  infer_instance

end Prod

end Module

namespace ModuleCat

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) [∀ i, Ring (Ri i)]
variable (Mi : ∀ i, ModuleCat.{uM} (Ri i)ᵐᵒᵖ)

/-- A family of right factor modules, bundled with its canonical pointwise
right action by the coefficient product. -/
def piRight : ModuleCat.{max uι uM} (∀ i, Ri i)ᵐᵒᵖ :=
  letI : Module (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i) :=
    Module.piRightModule Ri (fun i => Mi i)
  ModuleCat.of (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i)

/-- The bundled product has the ordinary dependent function carrier. -/
theorem piRight_carrier : (piRight Ri Mi : Type (max uι uM)) = (∀ i, Mi i) := by
  rfl

/-- Form an element of the bundled right coefficient product from its values. -/
def piRightMk (x : ∀ i, Mi i) : piRight Ri Mi := x

/-- Formation retains every coordinate. -/
theorem piRightMk_apply (x : ∀ i, Mi i) (i : ι) : piRightMk Ri Mi x i = x i := by
  rfl

/-- Equality in the bundled product is detected by ordinary function evaluation. -/
theorem piRight_ext_iff (x y : piRight Ri Mi) : x = y ↔ ∀ i, x i = y i := by
  exact funext_iff

/-- Scalar evaluation uses the corresponding factor's right action. -/
theorem piRight_smul_apply (a : ∀ i, Ri i) (x : piRight Ri Mi) (i : ι) :
    (MulOpposite.op a • x) i = MulOpposite.op (a i) • x i := by
  exact Module.piRightModule_smul_apply Ri (fun j => Mi j) a x i

/-- Zero is evaluated pointwise. -/
theorem piRight_zero_apply (i : ι) : (0 : piRight Ri Mi) i = 0 := by
  rfl

/-- Addition is evaluated pointwise. -/
theorem piRight_add_apply (x y : piRight Ri Mi) (i : ι) : (x + y) i = x i + y i := by
  rfl

/-- Negation is evaluated pointwise at Ring scope. -/
theorem piRight_neg_apply (x : piRight Ri Mi) (i : ι) : (-x) i = -x i := by
  rfl

/-- The accessible semilinear evaluation map of the bundled product. -/
def piRightEval (i : ι) : piRight Ri Mi →ₛₗ[RingHom.op (Pi.evalRingHom Ri i)] Mi i :=
  Module.piRightEval Ri (fun i => Mi i) i

/-- Bundled semilinear evaluation is function application. -/
theorem piRightEval_apply (i : ι) (x : piRight Ri Mi) : piRightEval Ri Mi i x = x i := by
  exact Module.piRightEval_apply Ri (fun j => Mi j) i x

/-- The supported element with a prescribed value at one coordinate. No
finiteness or public decidable-equality hypothesis is needed for its formation. -/
noncomputable def piRightSingle (i : ι) (x : Mi i) : piRight Ri Mi :=
  @Pi.single ι (fun i => Mi i) (fun _ => inferInstance) (Classical.decEq ι) i x

/-- A supported zero value is the zero element of the coefficient product. -/
@[simp]
theorem piRightSingle_zero (i : ι) : piRightSingle Ri Mi i 0 = 0 := by
  classical
  exact Pi.single_zero (M := fun j => (Mi j : Type uM)) i

/-- Supported formation preserves addition of coordinate values. -/
theorem piRightSingle_add (i : ι) (x y : Mi i) :
    piRightSingle Ri Mi i (x + y) = piRightSingle Ri Mi i x + piRightSingle Ri Mi i y := by
  classical
  exact Pi.single_add (f := fun j => (Mi j : Type uM)) i x y

/-- A supported element evaluates to its prescribed value at its own coordinate. -/
theorem piRightSingle_apply_same (i : ι) (x : Mi i) : piRightSingle Ri Mi i x i = x := by
  classical
  exact Pi.single_eq_same (M := fun j => (Mi j : Type uM)) i x

/-- A supported element vanishes at every other coordinate. -/
theorem piRightSingle_apply_ne (i j : ι) (h : j ≠ i) (x : Mi i) :
    piRightSingle Ri Mi i x j = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun k => (Mi k : Type uM)) h x

/-- Supported formation respects right scalars through their coordinate values. -/
theorem piRightSingle_smul (a : ∀ i, Ri i) (i : ι) (x : Mi i) :
    piRightSingle Ri Mi i (MulOpposite.op (a i) • x) =
      MulOpposite.op a • piRightSingle Ri Mi i x := by
  classical
  apply (piRight_ext_iff Ri Mi _ _).2
  intro j
  by_cases h : j = i
  · subst j
    simp only [piRight_smul_apply, piRightSingle_apply_same]
  · simp only [piRight_smul_apply, piRightSingle_apply_ne Ri Mi i j h, smul_zero]

/-- A coefficient-product module whose other factors are zero is linearly equivalent
to its selected factor, restricted along the opposite coordinate projection.
The index need not be finite, and the two carriers may have different universes. -/
noncomputable def piRightLinearEquivOfIsZero (i : ι)
    (h : ∀ j, j ≠ i → CategoryTheory.Limits.IsZero (Mi j)) :
    piRight Ri Mi ≃ₗ[(∀ j, Ri j)ᵐᵒᵖ]
      (ModuleCat.restrictScalars (RingHom.op (Pi.evalRingHom Ri i))).obj (Mi i) where
  toFun x := x i
  invFun y := piRightSingle Ri Mi i y
  left_inv x := by
    apply (piRight_ext_iff Ri Mi _ _).2
    intro j
    by_cases hj : j = i
    · subst j
      exact piRightSingle_apply_same Ri Mi i (x i)
    · let : Subsingleton (Mi j) := subsingleton_of_isZero (h j hj)
      exact Subsingleton.elim _ _
  right_inv y := piRightSingle_apply_same Ri Mi i y
  map_add' _ _ := rfl
  map_smul' a x := piRight_smul_apply Ri Mi a.unop x i

/-- The supported-product comparison evaluates at the selected coordinate. -/
@[simp]
theorem piRightLinearEquivOfIsZero_apply (i : ι)
    (h : ∀ j, j ≠ i → CategoryTheory.Limits.IsZero (Mi j)) (x : piRight Ri Mi) :
    piRightLinearEquivOfIsZero Ri Mi i h x = x i := rfl

/-- The inverse comparison inserts a value at the selected coordinate. -/
@[simp]
theorem piRightLinearEquivOfIsZero_symm_apply (i : ι)
    (h : ∀ j, j ≠ i → CategoryTheory.Limits.IsZero (Mi j))
    (y : (ModuleCat.restrictScalars (RingHom.op (Pi.evalRingHom Ri i))).obj (Mi i)) :
    (piRightLinearEquivOfIsZero Ri Mi i h).symm y = piRightSingle Ri Mi i y := rfl

/-- A finite coefficient-product module is reconstructed from its supported
coordinates. The finite sum requires no chosen enumeration. -/
theorem piRight_eq_finsum_single [Finite ι] (x : piRight Ri Mi) :
    x = ∑ᶠ i, piRightSingle Ri Mi i (x i) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [finsum_eq_sum_of_fintype]
  change (x : ∀ i, Mi i) = ∑ i, Pi.single i (x i)
  exact (Finset.univ_sum_single (x : ∀ i, Mi i)).symm

/-- Factorwise right-linear equivalence of the bundled coefficient products. -/
def piRightCongr (Ni : ∀ i, ModuleCat.{uN} (Ri i)ᵐᵒᵖ)
    (e : ∀ i, Mi i ≃ₗ[(Ri i)ᵐᵒᵖ] Ni i) :
    piRight Ri Mi ≃ₗ[(∀ i, Ri i)ᵐᵒᵖ] piRight Ri Ni :=
  Module.piRightCongr Ri (fun i => Mi i) (fun i => Ni i) e

/-- The bundled assembled equivalence has the factorwise forward values. -/
theorem piRightCongr_apply (Ni : ∀ i, ModuleCat.{uN} (Ri i)ᵐᵒᵖ)
    (e : ∀ i, Mi i ≃ₗ[(Ri i)ᵐᵒᵖ] Ni i) (x : piRight Ri Mi) (i : ι) :
    piRightCongr Ri Mi Ni e x i = e i (x i) := by
  exact Module.piRightCongr_apply Ri (fun j => Mi j) (fun j => Ni j) e x i

/-- Binary direct sum commutes with the bundled coefficient-product assembly. -/
def piRightProdLinearEquiv (Ni : ∀ i, ModuleCat.{uN} (Ri i)ᵐᵒᵖ) :
    piRight Ri (fun i => ModuleCat.of (Ri i)ᵐᵒᵖ (Mi i × Ni i)) ≃ₗ[(∀ i, Ri i)ᵐᵒᵖ]
      (piRight Ri Mi × piRight Ri Ni) :=
  Module.piRightProdLinearEquiv Ri (fun i => Mi i) (fun i => Ni i)

/-- The bundled direct-sum comparison separates the two families. -/
theorem piRightProdLinearEquiv_apply (Ni : ∀ i, ModuleCat.{uN} (Ri i)ᵐᵒᵖ)
    (x : piRight Ri (fun i => ModuleCat.of (Ri i)ᵐᵒᵖ (Mi i × Ni i))) :
    piRightProdLinearEquiv Ri Mi Ni x =
      (fun i => (x i).1, fun i => (x i).2) := by
  exact Module.piRightProdLinearEquiv_apply Ri (fun j => Mi j) (fun j => Ni j) x

end Pi

section Prod

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]
variable (M : ModuleCat.{uM} Rᵐᵒᵖ) (N : ModuleCat.{uN} Sᵐᵒᵖ)

/-- The independently sized binary right-module bundle, with its ordinary pair
carrier and the canonical coordinatewise action. -/
def prodRight : ModuleCat.{max uM uN} (R × S)ᵐᵒᵖ :=
  letI : Module (R × S)ᵐᵒᵖ (M × N) := Module.prodRightModule R S M N
  ModuleCat.of (R × S)ᵐᵒᵖ (M × N)

/-- The binary bundle has the ordinary pair carrier. -/
theorem prodRight_carrier :
    (prodRight R S M N : Type (max uM uN)) =
      @Prod.{uM, uN} (M : Type uM) (N : Type uN) := by
  rfl

/-- Form a binary right-product element from its two values. -/
def prodRightMk (m : M) (n : N) : prodRight R S M N := (m, n)

/-- Binary formation retains its two coordinates. -/
theorem prodRightMk_apply (m : M) (n : N) : prodRightMk R S M N m n = (m, n) := by
  rfl

/-- The bundled binary action is pointwise. -/
theorem prodRight_smul (r : R) (s : S) (x : prodRight R S M N) :
    MulOpposite.op (r, s) • x = (MulOpposite.op r • x.1, MulOpposite.op s • x.2) := by
  exact Module.prodRightModule_smul R S M N r s x.1 x.2

/-- Equality in the binary bundle is detected by its two coordinates. -/
theorem prodRight_ext_iff (x y : prodRight R S M N) :
    x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := by
  exact Prod.ext_iff

/-- First-coordinate evaluation is semilinear along the opposite first projection. -/
def prodRightFst : prodRight R S M N →ₛₗ[RingHom.op (RingHom.fst R S)] M where
  toFun x := x.1
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    exact congrArg Prod.fst (prodRight_smul R S M N a.unop.1 a.unop.2 x)

/-- Second-coordinate evaluation is semilinear along the opposite second projection. -/
def prodRightSnd : prodRight R S M N →ₛₗ[RingHom.op (RingHom.snd R S)] N where
  toFun x := x.2
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    exact congrArg Prod.snd (prodRight_smul R S M N a.unop.1 a.unop.2 x)

/-- First-coordinate evaluation is ordinary pair projection. -/
theorem prodRightFst_apply (x : prodRight R S M N) : prodRightFst R S M N x = x.1 := by
  rfl

/-- Second-coordinate evaluation is ordinary pair projection. -/
theorem prodRightSnd_apply (x : prodRight R S M N) : prodRightSnd R S M N x = x.2 := by
  rfl

end Prod

namespace FiniteProjective

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) [∀ i, Ring (Ri i)]
variable (Mi : ∀ i, FiniteProjective.{uR, uM} (Ri i)ᵐᵒᵖ)

/-- A finite family of finite-projective right factor modules, assembled on the
ordinary function carrier with the canonical right coefficient-product action. -/
noncomputable def pi [Finite ι] :
    FiniteProjective.{max uι uR, max uι uM} (∀ i, Ri i)ᵐᵒᵖ :=
  ⟨ModuleCat.piRight Ri (fun i => (Mi i).obj), ⟨by
    let : ∀ i, Module.Finite (Ri i)ᵐᵒᵖ (Mi i).obj := fun i => (Mi i).property.1
    exact Module.finite_piRight Ri (fun i => (Mi i).obj), by
    let : ∀ i, Module.Projective (Ri i)ᵐᵒᵖ (Mi i).obj := fun i => (Mi i).property.2
    exact Module.projective_piRight Ri (fun i => (Mi i).obj)⟩⟩

variable [Finite ι]

/-- The finite-projective Pi object is the canonical coefficient-product bundle. -/
theorem pi_obj : (pi Ri Mi).obj = ModuleCat.piRight Ri (fun i => (Mi i).obj) := by
  rfl

/-- Its carrier is the ordinary family of input module carriers. -/
theorem pi_carrier : (pi Ri Mi : Type (max uι uM)) = (∀ i, Mi i) := by
  exact ModuleCat.piRight_carrier Ri (fun i => (Mi i).obj)

/-- Form an element of the finite-projective coefficient product. -/
def piMk (x : ∀ i, Mi i) : pi Ri Mi := x

/-- Finite-projective formation preserves coordinate values. -/
theorem piMk_apply (x : ∀ i, Mi i) (i : ι) : piMk Ri Mi x i = x i := by
  rfl

/-- Equality in the finite-projective Pi bundle is detected by its coordinates. -/
theorem pi_ext_iff (x y : pi Ri Mi) : x = y ↔ ∀ i, x i = y i := by
  exact ModuleCat.piRight_ext_iff Ri (fun i => (Mi i).obj) x y

/-- The finite-projective coefficient-product action is the canonical pointwise
right action, not an additional projectivity hypothesis. -/
theorem pi_smul_apply (a : ∀ i, Ri i) (x : pi Ri Mi) (i : ι) :
    (MulOpposite.op a • x) i = MulOpposite.op (a i) • x i := by
  exact ModuleCat.piRight_smul_apply Ri (fun i => (Mi i).obj) a x i

/-- The underlying finite-projective bundle is linearly equivalent to its
coefficient-product module bundle by the identity on functions. -/
def piLinearEquiv : pi Ri Mi ≃ₗ[(∀ i, Ri i)ᵐᵒᵖ]
    ModuleCat.piRight Ri (fun i => (Mi i).obj) :=
  LinearEquiv.refl (∀ i, Ri i)ᵐᵒᵖ (ModuleCat.piRight Ri (fun i => (Mi i).obj))

/-- The carrier comparison preserves each function value. -/
theorem piLinearEquiv_apply (x : pi Ri Mi) (i : ι) :
    piLinearEquiv Ri Mi x i = x i := by
  rfl

/-- The inverse carrier comparison preserves each function value. -/
theorem piLinearEquiv_symm_apply
    (x : ModuleCat.piRight Ri (fun i => (Mi i).obj)) (i : ι) :
    (piLinearEquiv Ri Mi).symm x i = x i := by
  rfl

/-- The finite-projective product is the finite sum of its supported coordinates,
using the accessible comparison with the ordinary coefficient-product bundle. -/
theorem pi_eq_finsum_single (x : pi Ri Mi) :
    x = ∑ᶠ i, (piLinearEquiv Ri Mi).symm
      (ModuleCat.piRightSingle Ri (fun j => (Mi j).obj) i (x i)) := by
  calc
    x = (piLinearEquiv Ri Mi).symm (piLinearEquiv Ri Mi x) :=
      ((piLinearEquiv Ri Mi).symm_apply_apply x).symm
    _ = (piLinearEquiv Ri Mi).symm
        (∑ᶠ i, ModuleCat.piRightSingle Ri (fun j => (Mi j).obj) i
          ((piLinearEquiv Ri Mi x) i)) :=
      congrArg (piLinearEquiv Ri Mi).symm
        (ModuleCat.piRight_eq_finsum_single Ri (fun i => (Mi i).obj)
          (piLinearEquiv Ri Mi x))
    _ = ∑ᶠ i, (piLinearEquiv Ri Mi).symm
        (ModuleCat.piRightSingle Ri (fun j => (Mi j).obj) i
          ((piLinearEquiv Ri Mi x) i)) :=
      (piLinearEquiv Ri Mi).symm.toAddEquiv.map_finsum _
    _ = _ :=
      finsum_congr fun i => congrArg
        (fun z : (Mi i).obj => (piLinearEquiv Ri Mi).symm
          (ModuleCat.piRightSingle Ri (fun j => (Mi j).obj) i z))
        (piLinearEquiv_apply Ri Mi x i)

end Pi

section Prod

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]
variable (M : FiniteProjective.{uR, uM} Rᵐᵒᵖ) (N : FiniteProjective.{uS, uN} Sᵐᵒᵖ)

/-- A finite-projective binary right-module product with independent coefficient
and carrier universes. Its finiteness and projectivity are output properties. -/
noncomputable def prodRight :
    FiniteProjective.{max uR uS, max uM uN} (R × S)ᵐᵒᵖ :=
  ⟨ModuleCat.prodRight R S M.obj N.obj, ⟨by
    let : Module.Finite Rᵐᵒᵖ M.obj := M.property.1
    let : Module.Finite Sᵐᵒᵖ N.obj := N.property.1
    exact Module.finite_prodRight R S M.obj N.obj, by
    let : Module.Projective Rᵐᵒᵖ M.obj := M.property.2
    let : Module.Projective Sᵐᵒᵖ N.obj := N.property.2
    exact Module.projective_prodRight R S M.obj N.obj⟩⟩

/-- The binary finite-projective object's module bundle is the canonical product. -/
theorem prodRight_obj : (prodRight R S M N).obj = ModuleCat.prodRight R S M.obj N.obj := by
  rfl

/-- The binary finite-projective carrier is the ordinary pair carrier. -/
theorem prodRight_carrier :
    (prodRight R S M N : Type (max uM uN)) =
      @Prod.{uM, uN} (M : Type uM) (N : Type uN) := by
  exact ModuleCat.prodRight_carrier R S M.obj N.obj

/-- Form a binary finite-projective product element from its values. -/
def prodRightMk (m : M) (n : N) : prodRight R S M N := (m, n)

/-- Binary finite-projective formation retains its coordinates. -/
theorem prodRightMk_apply (m : M) (n : N) :
    prodRightMk R S M N m n = (m, n) := by
  rfl

/-- Equality in the binary finite-projective product is detected by both values. -/
theorem prodRight_ext_iff (x y : prodRight R S M N) :
    x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := by
  exact ModuleCat.prodRight_ext_iff R S M.obj N.obj x y

/-- The binary finite-projective action is coordinatewise. -/
theorem prodRight_smul (r : R) (s : S) (x : prodRight R S M N) :
    MulOpposite.op (r, s) • x = (MulOpposite.op r • x.1, MulOpposite.op s • x.2) := by
  exact ModuleCat.prodRight_smul R S M.obj N.obj r s x

/-- The binary finite-projective carrier comparison is the identity on pairs. -/
def prodRightLinearEquiv : prodRight R S M N ≃ₗ[(R × S)ᵐᵒᵖ]
    ModuleCat.prodRight R S M.obj N.obj :=
  LinearEquiv.refl (R × S)ᵐᵒᵖ (ModuleCat.prodRight R S M.obj N.obj)

/-- The binary carrier comparison retains both coordinates. -/
theorem prodRightLinearEquiv_apply (x : prodRight R S M N) :
    prodRightLinearEquiv R S M N x = (x.1, x.2) := by
  exact Prod.ext rfl rfl

/-- An element of the binary finite-projective product is the sum of its two
supported values. -/
theorem prodRight_eq_add (x : prodRight R S M N) :
    x = prodRightMk R S M N x.1 0 + prodRightMk R S M N 0 x.2 := by
  simp only [prodRightMk_apply]
  exact (Prod.fst_add_snd x).symm

end Prod

end FiniteProjective

namespace RightExtension

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) [∀ i, Ring (Ri i)]

/-- An arbitrary right module over a finite coefficient product is reconstructed
from its right scalar extensions along all coordinate projections. -/
noncomputable def piLinearEquiv [Finite ι]
    (M : ModuleCat.{uM} (∀ i, Ri i)ᵐᵒᵖ) :
    M ≃ₗ[(∀ i, Ri i)ᵐᵒᵖ] ModuleCat.piRight Ri
      (fun i => ModuleCat.of (Ri i)ᵐᵒᵖ (Obj (Pi.evalRingHom Ri i) M)) := by
  classical
  letI := Fintype.ofFinite ι
  let Ei := fun i => ModuleCat.of (Ri i)ᵐᵒᵖ (Obj (Pi.evalRingHom Ri i) M)
  let q : ∀ i, Obj (Pi.evalRingHom Ri i) M →+ M := fun i => by
    letI : Module (∀ j, Ri j) (Ri i) := (Pi.evalRingHom Ri i).toModule
    exact BalancedTensorProduct.lift (R := ∀ j, Ri j) (M := M) (N := Ri i)
      { toFun := fun m r => MulOpposite.op (Pi.single i r) • m
        map_zero_left := fun r => smul_zero _
        map_add_left := fun m n r => smul_add _ m n
        map_zero_right := fun m => by simp
        map_add_right := fun m r s => by
          rw [Pi.single_add, MulOpposite.op_add, add_smul]
        balance := fun a m r => by
          change MulOpposite.op (Pi.single i r) • (MulOpposite.op a • m) =
            MulOpposite.op (Pi.single i (a i * r)) • m
          rw [← mul_smul]
          change MulOpposite.op (a * Pi.single i r) • m =
            MulOpposite.op (Pi.single i (a i * r)) • m
          rw [Pi.single_mul_right r] }
  have q_tmul : ∀ i (m : M) (r : Ri i),
      q i (tmul (Pi.evalRingHom Ri i) m r) = MulOpposite.op (Pi.single i r) • m := by
    intro i m r
    let _ : Module (∀ j, Ri j) (Ri i) := (Pi.evalRingHom Ri i).toModule
    exact BalancedTensorProduct.lift_tmul (R := ∀ j, Ri j) (M := M) (N := Ri i) _ m r
  have q_smul : ∀ i (a : ∀ j, Ri j) (z : Obj (Pi.evalRingHom Ri i) M),
      q i (MulOpposite.op (a i) • z) = MulOpposite.op a • q i z := by
    intro i a z
    let _ : Module (∀ j, Ri j) (Ri i) := (Pi.evalRingHom Ri i).toModule
    induction z using BalancedTensorProduct.induction_on with
    | zero => simp
    | pure m r =>
        change q i (MulOpposite.op (a i) • tmul (Pi.evalRingHom Ri i) m r) =
          MulOpposite.op a • q i (tmul (Pi.evalRingHom Ri i) m r)
        rw [tmul_smul, q_tmul, q_tmul]
        change MulOpposite.op (Pi.single i (r * a i)) • m =
          MulOpposite.op a • (MulOpposite.op (Pi.single i r) • m)
        rw [← mul_smul]
        change MulOpposite.op (Pi.single i (r * a i)) • m =
          MulOpposite.op (Pi.single i r * a) • m
        rw [Pi.single_mul_left r]
    | neg z hz =>
        rw [smul_neg, (q i).map_neg, hz, (q i).map_neg, smul_neg]
    | add z w hz hw =>
        rw [smul_add, (q i).map_add, hz, hw, (q i).map_add, smul_add]
  let T : M →ₗ[(∀ i, Ri i)ᵐᵒᵖ] ModuleCat.piRight Ri Ei :=
    { toFun := fun m i => tmul (Pi.evalRingHom Ri i) m 1
      map_add' := fun m n => by
        apply funext
        intro i
        exact (tmulOne (Pi.evalRingHom Ri i)).map_add m n
      map_smul' := fun a m => by
        apply (ModuleCat.piRight_ext_iff Ri Ei _ _).2
        intro i
        change tmul (Pi.evalRingHom Ri i) (a • m) 1 =
          MulOpposite.op ((MulOpposite.unop a) i) • tmul (Pi.evalRingHom Ri i) m 1
        exact (tmulOne (Pi.evalRingHom Ri i)).map_smulₛₗ a m }
  let Q : ModuleCat.piRight Ri Ei →ₗ[(∀ i, Ri i)ᵐᵒᵖ] M :=
    { toFun := fun x => ∑ i, q i (x i)
      map_add' := fun x y => by
        calc
          (∑ i, q i ((x + y) i)) = ∑ i, q i (x i + y i) := by
            apply Finset.sum_congr rfl
            intro i _
            exact congrArg (q i) (ModuleCat.piRight_add_apply Ri Ei x y i)
          _ = ∑ i, (q i (x i) + q i (y i)) := by
            apply Finset.sum_congr rfl
            intro i _
            exact (q i).map_add (x i) (y i)
          _ = _ := Finset.sum_add_distrib
      map_smul' := fun a x => by
        change (∑ i, q i ((a • x) i)) = a • ∑ i, q i (x i)
        calc
          (∑ i, q i ((a • x) i)) = ∑ i, a • q i (x i) := by
            apply Finset.sum_congr rfl
            intro i _
            calc
              q i ((a • x) i) =
                  q i (MulOpposite.op ((MulOpposite.unop a) i) • x i) :=
                congrArg (q i)
                  (ModuleCat.piRight_smul_apply Ri Ei (MulOpposite.unop a) x i)
              _ = MulOpposite.op (MulOpposite.unop a) • q i (x i) :=
                q_smul i (MulOpposite.unop a) (x i)
              _ = a • q i (x i) :=
                congrArg (fun b : (∀ j, Ri j)ᵐᵒᵖ => b • q i (x i))
                  (MulOpposite.op_unop a)
          _ = _ := (Finset.smul_sum (r := a) (f := fun i => q i (x i))
            (s := Finset.univ)).symm }
  have hcoord : ∀ i (z : Obj (Pi.evalRingHom Ri i) M),
      T (q i z) = ModuleCat.piRightSingle Ri Ei i z := by
    intro i z
    let si : Obj (Pi.evalRingHom Ri i) M →+ ModuleCat.piRight Ri Ei :=
      { toFun := ModuleCat.piRightSingle Ri Ei i
        map_zero' := ModuleCat.piRightSingle_zero Ri Ei i
        map_add' := fun x y => ModuleCat.piRightSingle_add Ri Ei i x y }
    let _ : Module (∀ j, Ri j) (Ri i) := (Pi.evalRingHom Ri i).toModule
    exact DFunLike.congr_fun
      (BalancedTensorProduct.hom_ext (R := ∀ j, Ri j) (M := M) (N := Ri i)
        (g := T.toAddMonoidHom.comp (q i)) (h := si) fun m r => by
          change T (q i (tmul (Pi.evalRingHom Ri i) m r)) =
            ModuleCat.piRightSingle Ri Ei i (tmul (Pi.evalRingHom Ri i) m r)
          rw [q_tmul]
          apply funext
          intro j
          change tmul (Pi.evalRingHom Ri j) (MulOpposite.op (Pi.single i r) • m) 1 =
            ModuleCat.piRightSingle Ri Ei i (tmul (Pi.evalRingHom Ri i) m r) j
          rw [smul_tmul]
          by_cases h : j = i
          · subst j
            rw [ModuleCat.piRightSingle_apply_same]
            change tmul (Pi.evalRingHom Ri i) m ((Pi.single i r) i * 1) =
              tmul (Pi.evalRingHom Ri i) m r
            rw [Pi.single_eq_same, mul_one]
          · rw [ModuleCat.piRightSingle_apply_ne Ri Ei i j h]
            change tmul (Pi.evalRingHom Ri j) m ((Pi.single i r) j * 1) = 0
            rw [Pi.single_eq_of_ne h, zero_mul]
            simp [tmul]) z
  have hid : (∑ i, Pi.single i (1 : Ri i)) = (1 : ∀ i, Ri i) := by
    apply funext
    intro j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · exact Pi.single_eq_same j 1
    · intro i _ h
      exact Pi.single_eq_of_ne h.symm 1
    · simp
  refine
    { __ := T
      invFun := Q
      left_inv := ?_
      right_inv := ?_ }
  · intro m
    change (∑ i, q i (tmul (Pi.evalRingHom Ri i) m 1)) = m
    simp_rw [q_tmul]
    rw [← Finset.sum_smul]
    calc
      (∑ i, MulOpposite.op (Pi.single i (1 : Ri i))) • m =
          MulOpposite.op (∑ i, Pi.single i (1 : Ri i)) • m :=
        congrArg (fun a : (∀ i, Ri i)ᵐᵒᵖ => a • m)
          (map_sum (MulOpposite.opAddEquiv : (∀ i, Ri i) ≃+ (∀ i, Ri i)ᵐᵒᵖ)
            (fun i => Pi.single i (1 : Ri i)) Finset.univ).symm
      _ = m := by rw [hid]; simp
  · intro x
    change T (∑ i, q i (x i)) = x
    rw [map_sum]
    simp_rw [hcoord]
    have hx := ModuleCat.piRight_eq_finsum_single Ri Ei x
    rw [finsum_eq_sum_of_fintype] at hx
    exact hx.symm

/-- Every reconstruction coordinate is the canonical tensor with coefficient one. -/
theorem piLinearEquiv_apply [Finite ι]
    (M : ModuleCat.{uM} (∀ i, Ri i)ᵐᵒᵖ) (m : M) (i : ι) :
    piLinearEquiv Ri M m i = tmul (Pi.evalRingHom Ri i) m 1 := by
  rfl

/-- The inverse reconstruction on a supported pure tensor is the corresponding
supported scalar acting on the original module. The supported scalar is not a
unital ring homomorphism into the coefficient product. -/
theorem piLinearEquiv_symm_single_tmul [Finite ι]
    (M : ModuleCat.{uM} (∀ i, Ri i)ᵐᵒᵖ) (i : ι) (m : M) (r : Ri i) :
    (piLinearEquiv Ri M).symm
        (ModuleCat.piRightSingle Ri
          (fun j => ModuleCat.of (Ri j)ᵐᵒᵖ (Obj (Pi.evalRingHom Ri j) M))
          i (tmul (Pi.evalRingHom Ri i) m r)) =
      MulOpposite.op
        (@Pi.single ι Ri (fun _ => inferInstance) (Classical.decEq ι) i r) • m := by
  classical
  apply (piLinearEquiv Ri M).injective
  rw [LinearEquiv.apply_symm_apply]
  apply funext
  intro j
  rw [piLinearEquiv_apply, smul_tmul]
  by_cases h : j = i
  · subst j
    rw [ModuleCat.piRightSingle_apply_same]
    change tmul (Pi.evalRingHom Ri i) m r =
      tmul (Pi.evalRingHom Ri i) m ((Pi.single i r) i * 1)
    rw [Pi.single_eq_same, mul_one]
  · rw [ModuleCat.piRightSingle_apply_ne Ri
      (fun j => ModuleCat.of (Ri j)ᵐᵒᵖ (Obj (Pi.evalRingHom Ri j) M)) i j h]
    change 0 = tmul (Pi.evalRingHom Ri j) m ((Pi.single i r) j * 1)
    rw [Pi.single_eq_of_ne h, zero_mul]
    simp [tmul]

/-- Inverse reconstruction is the finite sum of inverse supported coordinates. -/
theorem piLinearEquiv_symm_eq_finsum [Finite ι]
    (M : ModuleCat.{uM} (∀ i, Ri i)ᵐᵒᵖ)
    (x : ModuleCat.piRight Ri
      (fun i => ModuleCat.of (Ri i)ᵐᵒᵖ (Obj (Pi.evalRingHom Ri i) M))) :
    (piLinearEquiv Ri M).symm x = ∑ᶠ i, (piLinearEquiv Ri M).symm
      (ModuleCat.piRightSingle Ri
        (fun j => ModuleCat.of (Ri j)ᵐᵒᵖ (Obj (Pi.evalRingHom Ri j) M)) i (x i)) := by
  calc
    (piLinearEquiv Ri M).symm x = (piLinearEquiv Ri M).symm
        (∑ᶠ i, ModuleCat.piRightSingle Ri
          (fun j => ModuleCat.of (Ri j)ᵐᵒᵖ (Obj (Pi.evalRingHom Ri j) M)) i (x i)) :=
      congrArg (piLinearEquiv Ri M).symm
        (ModuleCat.piRight_eq_finsum_single Ri _ x)
    _ = _ := (piLinearEquiv Ri M).symm.toAddEquiv.map_finsum _

/-- Coordinate extension of a coefficient-product family recovers that factor.
The index need not be finite. -/
noncomputable def piRecoverLinearEquiv
    (Mi : ∀ i, ModuleCat.{uM} (Ri i)ᵐᵒᵖ) (i : ι) :
    Obj (Pi.evalRingHom Ri i) (ModuleCat.piRight Ri Mi) ≃ₗ[(Ri i)ᵐᵒᵖ] Mi i := by
  classical
  refine
    { __ := fromSemilinear (Pi.evalRingHom Ri i) (ModuleCat.piRightEval Ri Mi i)
      invFun := fun y => tmul (Pi.evalRingHom Ri i) (ModuleCat.piRightSingle Ri Mi i y) 1
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    change tmul (Pi.evalRingHom Ri i)
      (ModuleCat.piRightSingle Ri Mi i
        (fromSemilinear (Pi.evalRingHom Ri i) (ModuleCat.piRightEval Ri Mi i) z)) 1 = z
    have hsurj : Function.Surjective (Pi.evalRingHom Ri i) := by
      intro r
      exact ⟨Pi.single i r, by simp⟩
    obtain ⟨x, hx⟩ := tmulOne_surjective (Pi.evalRingHom Ri i) hsurj z
    rw [← hx, tmulOne_apply, fromSemilinear_tmul, ModuleCat.piRightEval_apply]
    simp only [MulOpposite.op_one, one_smul]
    have hsingle : ModuleCat.piRightSingle Ri Mi i (x i) =
        MulOpposite.op (Pi.single i (1 : Ri i)) • x := by
      apply funext
      intro j
      rw [ModuleCat.piRight_smul_apply]
      by_cases h : j = i
      · subst j
        rw [ModuleCat.piRightSingle_apply_same, Pi.single_eq_same]
        simp
      · rw [ModuleCat.piRightSingle_apply_ne Ri Mi i j h, Pi.single_eq_of_ne h]
        simp
    rw [hsingle, smul_tmul]
    simp
  · intro y
    change fromSemilinear (Pi.evalRingHom Ri i) (ModuleCat.piRightEval Ri Mi i)
      (tmul (Pi.evalRingHom Ri i) (ModuleCat.piRightSingle Ri Mi i y) 1) = y
    rw [fromSemilinear_tmul, ModuleCat.piRightEval_apply,
      ModuleCat.piRightSingle_apply_same]
    simp

/-- Recovery evaluates a pure tensor in its chosen factor, with the target
coefficient acting on the right. -/
theorem piRecoverLinearEquiv_tmul
    (Mi : ∀ i, ModuleCat.{uM} (Ri i)ᵐᵒᵖ) (i : ι)
    (x : ModuleCat.piRight Ri Mi) (r : Ri i) :
    piRecoverLinearEquiv Ri Mi i (tmul (Pi.evalRingHom Ri i) x r) =
      MulOpposite.op r • x i := by
  exact fromSemilinear_tmul (Pi.evalRingHom Ri i) (ModuleCat.piRightEval Ri Mi i) x r

/-- The inverse recovery inserts a supported value and tensors with one. -/
theorem piRecoverLinearEquiv_symm_apply
    (Mi : ∀ i, ModuleCat.{uM} (Ri i)ᵐᵒᵖ) (i : ι) (y : Mi i) :
    (piRecoverLinearEquiv Ri Mi i).symm y =
      tmul (Pi.evalRingHom Ri i) (ModuleCat.piRightSingle Ri Mi i y) 1 := by
  rfl

/-- Equality of source module elements is detected by all coordinate
scalar extensions. This uses reconstruction without unfolding its construction. -/
theorem eq_iff_pi_tmulOne_eq [Finite ι]
    (M : ModuleCat.{uM} (∀ i, Ri i)ᵐᵒᵖ) (m n : M) :
    m = n ↔ ∀ i, tmulOne (Pi.evalRingHom Ri i) m = tmulOne (Pi.evalRingHom Ri i) n := by
  constructor
  · rintro rfl i
    rfl
  · intro h
    apply (piLinearEquiv Ri M).injective
    apply funext
    intro i
    simpa only [piLinearEquiv_apply, tmulOne_apply] using h i

end Pi

end RightExtension

end ModuleCat
