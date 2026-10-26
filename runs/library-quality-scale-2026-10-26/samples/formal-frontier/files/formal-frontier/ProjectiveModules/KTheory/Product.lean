/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.ScalarExtension
public import ProjectiveModules.Module.RightProduct
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Ring.Fin
import Mathlib.Algebra.Ring.ULift
import Mathlib.GroupTheory.MonoidLocalization.Lemmas

/-!
# Product rings: projective classes and K₀

Coordinate scalar extension defines `K0.piMap` for arbitrary families of rings.
For a finite family, this is the forward map of `K0.piEquiv`.

Coordinate scalar extension gives additive equivalences from the projective-class
monoid and K₀ of a finite product ring to the products of the corresponding
factor objects. The forward maps are `ProjectiveClass.map` and `K0.map` along
`Pi.evalRingHom`, or along `RingHom.fst` and `RingHom.snd` for binary products.

The index universe is independent of the scalar universe, and the binary factors
may have unrelated universes. Module-generator formulas allow arbitrary carrier
universes. The factors need not be commutative or nontrivial; empty families and
zero rings are included. No cancellation of projective classes, or injectivity
of the class-to-K₀ map, is required.

The API describes whole forward homomorphisms, coordinate homomorphisms, module
generators, compatibility with group completion, inverse signed presentations,
and equality detection. The ordinary additive-equivalence laws give preservation
of zero and addition, and, for K₀, subtraction and integer scalar multiplication.

## References and credits

* Mathlib's Pi and binary-product homomorphisms and additive equivalences.
* Mathlib's additive Grothendieck group and arbitrary-family product localization.
* Projective Modules' finite-projective classes, group-completion universal
  property, and right scalar-extension maps and module comparisons.
-/

@[expose] public section

universe uι uR uS uM uN

namespace KTheory

namespace ProjectiveClass

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) [∀ i, Ring (Ri i)]

/-- Coordinate scalar extension classifies finite projective right modules over
a finite product ring, as an additive equivalence of their isomorphism classes. -/
noncomputable def piEquiv [Finite ι] :
    ProjectiveClass (∀ i, Ri i) ≃+ (∀ i, ProjectiveClass (Ri i)) :=
  AddEquiv.ofBijective
    (AddMonoidHom.pi (fun i ↦ map (Pi.evalRingHom Ri i))) (by
      classical
      constructor
      · intro a b hab
        obtain ⟨M, rfl⟩ := of_surjective (∀ i, Ri i) a
        obtain ⟨N, rfl⟩ := of_surjective (∀ i, Ri i) b
        have hfactor (i : ι) : Nonempty
            (ModuleCat.RightExtension.Obj (Pi.evalRingHom Ri i) M ≃ₗ[(Ri i)ᵐᵒᵖ]
              ModuleCat.RightExtension.Obj (Pi.evalRingHom Ri i) N) := by
          apply (of_eq_iff (Ri i)
            (ModuleCat.RightExtension.Obj (Pi.evalRingHom Ri i) M)
            (ModuleCat.RightExtension.Obj (Pi.evalRingHom Ri i) N)).1
          have hi := congrFun hab i
          change map (Pi.evalRingHom Ri i) (of (∀ j, Ri j) M) =
            map (Pi.evalRingHom Ri i) (of (∀ j, Ri j) N) at hi
          simpa only [map_of] using hi
        let e := fun i => Classical.choice (hfactor i)
        apply (of_eq_iff (∀ i, Ri i) M N).2
        exact ⟨(ModuleCat.RightExtension.piLinearEquiv Ri M.obj).trans
          ((ModuleCat.piRightCongr Ri
            (fun i => ModuleCat.of (Ri i)ᵐᵒᵖ
              (ModuleCat.RightExtension.Obj (Pi.evalRingHom Ri i) M))
            (fun i => ModuleCat.of (Ri i)ᵐᵒᵖ
              (ModuleCat.RightExtension.Obj (Pi.evalRingHom Ri i) N)) e).trans
            (ModuleCat.RightExtension.piLinearEquiv Ri N.obj).symm)⟩
      · intro a
        have hrepr (i : ι) :
            ∃ X : ModuleCat.FiniteProjective.{uR, uR} (Ri i)ᵐᵒᵖ,
              of (Ri i) X = a i := of_surjective (Ri i) (a i)
        choose Mi hMi using hrepr
        refine ⟨of (∀ i, Ri i) (ModuleCat.FiniteProjective.pi Ri Mi), ?_⟩
        funext i
        change map (Pi.evalRingHom Ri i)
          (of (∀ j, Ri j) (ModuleCat.FiniteProjective.pi Ri Mi)) = a i
        rw [map_of]
        calc
          of (Ri i) (ModuleCat.RightExtension.Obj (Pi.evalRingHom Ri i)
              (ModuleCat.FiniteProjective.pi Ri Mi)) = of (Ri i) (Mi i) :=
            of_eq_of_equiv (Ri i) _
              ((ModuleCat.RightExtension.mapLinearEquiv (Pi.evalRingHom Ri i)
                (ModuleCat.FiniteProjective.piLinearEquiv Ri Mi)).trans
                (ModuleCat.RightExtension.piRecoverLinearEquiv Ri
                  (fun j => (Mi j).obj) i))
          _ = a i := hMi i)

variable [Finite ι]

/-- The whole forward homomorphism is the family of coordinate scalar-extension
homomorphisms. -/
theorem piEquiv_toAddMonoidHom :
    (piEquiv Ri).toAddMonoidHom =
      AddMonoidHom.pi (fun i ↦ map (Pi.evalRingHom Ri i)) := by
  rfl

/-- Composing the decomposition with coordinate evaluation gives the
scalar-extension homomorphism for that coordinate. -/
theorem eval_comp_piEquiv (i : ι) :
    (Pi.evalAddMonoidHom (fun j ↦ ProjectiveClass (Ri j)) i).comp
        (piEquiv Ri).toAddMonoidHom = map (Pi.evalRingHom Ri i) := by
  rfl

/-- Evaluation of the class decomposition at any coordinate is scalar extension. -/
@[simp]
theorem piEquiv_apply (a : ProjectiveClass (∀ i, Ri i)) (i : ι) :
    piEquiv Ri a i = map (Pi.evalRingHom Ri i) a := by
  rfl

/-- A finite projective module in any carrier universe decomposes into the
classes of its coordinate right scalar extensions. -/
@[simp]
theorem piEquiv_of_module (M : Type uM) [AddCommGroup M]
    [Module (∀ i, Ri i)ᵐᵒᵖ M]
    [Module.Finite (∀ i, Ri i)ᵐᵒᵖ M] [Module.Projective (∀ i, Ri i)ᵐᵒᵖ M]
    (i : ι) :
    piEquiv Ri (of (∀ i, Ri i) M) i =
      of (Ri i) (ModuleCat.RightExtension.Obj (Pi.evalRingHom Ri i) M) := by
  simpa only [piEquiv_apply] using map_of (Pi.evalRingHom Ri i) M

/-- The inverse class decomposition of factor module generators is the class
of their canonical finite-projective coefficient product. -/
theorem piEquiv_symm_of_module
    (Mi : ∀ i, ModuleCat.FiniteProjective.{uR, uM} (Ri i)ᵐᵒᵖ) :
    (piEquiv Ri).symm (fun i ↦ of (Ri i) (Mi i)) =
      of (∀ i, Ri i) (ModuleCat.FiniteProjective.pi Ri Mi) := by
  apply (piEquiv Ri).injective
  rw [AddEquiv.apply_symm_apply]
  funext i
  change of (Ri i) (Mi i) = map (Pi.evalRingHom Ri i)
    (of (∀ j, Ri j) (ModuleCat.FiniteProjective.pi Ri Mi))
  rw [map_of]
  exact (of_eq_of_equiv (Ri i) _
    ((ModuleCat.RightExtension.mapLinearEquiv (Pi.evalRingHom Ri i)
      (ModuleCat.FiniteProjective.piLinearEquiv Ri Mi)).trans
      (ModuleCat.RightExtension.piRecoverLinearEquiv Ri
        (fun j => (Mi j).obj) i))).symm

/-- Reassembling all coordinate scalar-extension classes recovers the source
class. -/
theorem piEquiv_symm_apply_pi_map (a : ProjectiveClass (∀ i, Ri i)) :
    (piEquiv Ri).symm (fun i ↦ map (Pi.evalRingHom Ri i) a) = a := by
  change (piEquiv Ri).symm (piEquiv Ri a) = a
  exact (piEquiv Ri).symm_apply_apply a

/-- The coordinate scalar extensions of a reassembled family recover every
class in the given family. -/
theorem pi_map_piEquiv_symm (a : ∀ i, ProjectiveClass (Ri i)) :
    (fun i ↦ map (Pi.evalRingHom Ri i) ((piEquiv Ri).symm a)) = a := by
  change piEquiv Ri ((piEquiv Ri).symm a) = a
  exact (piEquiv Ri).apply_symm_apply a

/-- All coordinate scalar-extension maps together detect equality of classes. -/
theorem eq_iff_pi_map_eq (a b : ProjectiveClass (∀ i, Ri i)) :
    a = b ↔ ∀ i, map (Pi.evalRingHom Ri i) a = map (Pi.evalRingHom Ri i) b := by
  constructor
  · intro h
    subst b
    intro i
    rfl
  · intro h
    apply (piEquiv Ri).injective
    funext i
    exact h i

end Pi

section Prod

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]

/-- The two projection scalar extensions classify finite projective right
modules over a binary product of rings, with independently sized factors. -/
noncomputable def prodEquiv :
    ProjectiveClass (R × S) ≃+ (ProjectiveClass R × ProjectiveClass S) :=
  AddEquiv.ofBijective
    ((map (RingHom.fst R S)).prod (map (RingHom.snd R S))) (by
      let Rhat := ULift.{uS} R
      let Shat := ULift.{uR} S
      let Ri : Fin 2 → Type (max uR uS) := Fin.cases Rhat (fun _ => Shat)
      let : ∀ i, Ring (Ri i) := fun i =>
        Fin.cases (inferInstance : Ring Rhat)
          (fun j => Eq.mpr
            (congrArg Ring (show Ri j.succ = Shat from by
              simp only [Ri, Fin.cases_succ]))
            (inferInstance : Ring Shat)) i
      let pR : (∀ i, Ri i) →+* Rhat := Pi.evalRingHom Ri 0
      let pS : (∀ i, Ri i) →+* Shat := Pi.evalRingHom Ri 1
      let dR : Rhat ≃+* R := ULift.ringEquiv
      let dS : Shat ≃+* S := ULift.ringEquiv
      let q : (∀ i, Ri i) ≃+* R × S :=
        (RingEquiv.piFinTwo Ri).trans (RingEquiv.prodCongr dR dS)
      let eA : ProjectiveClass (R × S) ≃+ ProjectiveClass (∀ i, Ri i) :=
        { toFun := map q.symm.toRingHom
          invFun := map q.toRingHom
          left_inv := by
            intro a
            change ((map q.toRingHom).comp (map q.symm.toRingHom)) a = a
            rw [← map_comp, RingEquiv.toRingHom_comp_symm_toRingHom, map_id]
            rfl
          right_inv := by
            intro a
            change ((map q.symm.toRingHom).comp (map q.toRingHom)) a = a
            rw [← map_comp, RingEquiv.symm_toRingHom_comp_toRingHom, map_id]
            rfl
          map_add' := (map q.symm.toRingHom).map_add }
      let eR : ProjectiveClass Rhat ≃+ ProjectiveClass R :=
        { toFun := map dR.toRingHom
          invFun := map dR.symm.toRingHom
          left_inv := by
            intro a
            change ((map dR.symm.toRingHom).comp (map dR.toRingHom)) a = a
            rw [← map_comp, RingEquiv.symm_toRingHom_comp_toRingHom, map_id]
            rfl
          right_inv := by
            intro a
            change ((map dR.toRingHom).comp (map dR.symm.toRingHom)) a = a
            rw [← map_comp, RingEquiv.toRingHom_comp_symm_toRingHom, map_id]
            rfl
          map_add' := (map dR.toRingHom).map_add }
      let eS : ProjectiveClass Shat ≃+ ProjectiveClass S :=
        { toFun := map dS.toRingHom
          invFun := map dS.symm.toRingHom
          left_inv := by
            intro a
            change ((map dS.symm.toRingHom).comp (map dS.toRingHom)) a = a
            rw [← map_comp, RingEquiv.symm_toRingHom_comp_toRingHom, map_id]
            rfl
          right_inv := by
            intro a
            change ((map dS.toRingHom).comp (map dS.symm.toRingHom)) a = a
            rw [← map_comp, RingEquiv.toRingHom_comp_symm_toRingHom, map_id]
            rfl
          map_add' := (map dS.toRingHom).map_add }
      let pack : (∀ i, ProjectiveClass (Ri i)) ≃+
          (ProjectiveClass Rhat × ProjectiveClass Shat) :=
        (LinearEquiv.piFinTwo ℕ (fun i => ProjectiveClass (Ri i))).toAddEquiv
      let e : ProjectiveClass (R × S) ≃+ (ProjectiveClass R × ProjectiveClass S) :=
        eA.trans ((piEquiv Ri).trans (pack.trans (AddEquiv.prodCongr eR eS)))
      have hfst : dR.toRingHom.comp (pR.comp q.symm.toRingHom) =
          RingHom.fst R S := by
        ext x
        rfl
      have hsnd : dS.toRingHom.comp (pS.comp q.symm.toRingHom) =
          RingHom.snd R S := by
        ext x
        rfl
      have hforward : e.toAddMonoidHom =
          (map (RingHom.fst R S)).prod (map (RingHom.snd R S)) := by
        apply AddMonoidHom.ext
        intro a
        apply Prod.ext
        · change map dR.toRingHom (map pR (map q.symm.toRingHom a)) =
              map (RingHom.fst R S) a
          calc
            _ = map dR.toRingHom (map (pR.comp q.symm.toRingHom) a) :=
              congrArg (fun b : ProjectiveClass Rhat => map dR.toRingHom b)
                (DFunLike.congr_fun (map_comp q.symm.toRingHom pR) a).symm
            _ = map (dR.toRingHom.comp (pR.comp q.symm.toRingHom)) a :=
              (DFunLike.congr_fun
                (map_comp (pR.comp q.symm.toRingHom) dR.toRingHom) a).symm
            _ = map (RingHom.fst R S) a := by rw [hfst]
        · change map dS.toRingHom (map pS (map q.symm.toRingHom a)) =
              map (RingHom.snd R S) a
          calc
            _ = map dS.toRingHom (map (pS.comp q.symm.toRingHom) a) :=
              congrArg (fun b : ProjectiveClass Shat => map dS.toRingHom b)
                (DFunLike.congr_fun (map_comp q.symm.toRingHom pS) a).symm
            _ = map (dS.toRingHom.comp (pS.comp q.symm.toRingHom)) a :=
              (DFunLike.congr_fun
                (map_comp (pS.comp q.symm.toRingHom) dS.toRingHom) a).symm
            _ = map (RingHom.snd R S) a := by rw [hsnd]
      rw [← hforward]
      exact e.bijective)

/-- The whole forward homomorphism is the pair of projection scalar-extension
homomorphisms. -/
theorem prodEquiv_toAddMonoidHom :
    (prodEquiv R S).toAddMonoidHom =
      (map (RingHom.fst R S)).prod (map (RingHom.snd R S)) := by
  rfl

/-- The first component homomorphism is scalar extension along `RingHom.fst`. -/
theorem fst_comp_prodEquiv :
    (AddMonoidHom.fst (ProjectiveClass R) (ProjectiveClass S)).comp
        (prodEquiv R S).toAddMonoidHom = map (RingHom.fst R S) := by
  rfl

/-- The second component homomorphism is scalar extension along `RingHom.snd`. -/
theorem snd_comp_prodEquiv :
    (AddMonoidHom.snd (ProjectiveClass R) (ProjectiveClass S)).comp
        (prodEquiv R S).toAddMonoidHom = map (RingHom.snd R S) := by
  rfl

/-- The binary class decomposition evaluates by the two projection maps. -/
@[simp]
theorem prodEquiv_apply (a : ProjectiveClass (R × S)) :
    prodEquiv R S a = (map (RingHom.fst R S) a, map (RingHom.snd R S) a) := by
  rfl

/-- A finite projective module with an independent carrier universe gives the
pair of classes of its two right scalar extensions. -/
@[simp]
theorem prodEquiv_of_module (M : Type uM) [AddCommGroup M] [Module (R × S)ᵐᵒᵖ M]
    [Module.Finite (R × S)ᵐᵒᵖ M] [Module.Projective (R × S)ᵐᵒᵖ M] :
    prodEquiv R S (of (R × S) M) =
      (of R (ModuleCat.RightExtension.Obj (RingHom.fst R S) M),
        of S (ModuleCat.RightExtension.Obj (RingHom.snd R S) M)) := by
  simp only [prodEquiv_apply, map_of]

/-- The inverse binary class decomposition of module generators is the class
of their canonical right-module product, with independent carrier universes. -/
theorem prodEquiv_symm_of_module
    (M : ModuleCat.FiniteProjective.{uR, uM} Rᵐᵒᵖ)
    (N : ModuleCat.FiniteProjective.{uS, uN} Sᵐᵒᵖ) :
    (prodEquiv R S).symm (of R M, of S N) =
      of (R × S) (ModuleCat.FiniteProjective.prodRight R S M N) := by
  let eR : ModuleCat.RightExtension.Obj (RingHom.fst R S)
      (ModuleCat.prodRight R S M.obj N.obj) ≃ₗ[Rᵐᵒᵖ] M :=
    { __ := ModuleCat.RightExtension.fromSemilinear (RingHom.fst R S)
        (ModuleCat.prodRightFst R S M.obj N.obj)
      invFun := fun m => ModuleCat.RightExtension.tmul (RingHom.fst R S)
        (ModuleCat.prodRightMk R S M.obj N.obj m 0) 1
      left_inv := by
        intro z
        change ModuleCat.RightExtension.tmul (RingHom.fst R S)
          (ModuleCat.prodRightMk R S M.obj N.obj
            (ModuleCat.RightExtension.fromSemilinear (RingHom.fst R S)
              (ModuleCat.prodRightFst R S M.obj N.obj) z) 0) 1 = z
        obtain ⟨x, hx⟩ := ModuleCat.RightExtension.tmulOne_surjective (RingHom.fst R S)
          (fun r => ⟨(r, 0), rfl⟩) z
        rw [← hx, ModuleCat.RightExtension.tmulOne_apply,
          ModuleCat.RightExtension.fromSemilinear_tmul, ModuleCat.prodRightFst_apply]
        simp only [MulOpposite.op_one, one_smul]
        have hsupport : ModuleCat.prodRightMk R S M.obj N.obj x.1 0 =
            MulOpposite.op ((1 : R), (0 : S)) • x := by
          simp only [ModuleCat.prodRightMk_apply, ModuleCat.prodRight_smul,
            MulOpposite.op_one, MulOpposite.op_zero, one_smul, zero_smul]
          rfl
        rw [hsupport, ModuleCat.RightExtension.smul_tmul]
        simp
      right_inv := by
        intro m
        change ModuleCat.RightExtension.fromSemilinear (RingHom.fst R S)
          (ModuleCat.prodRightFst R S M.obj N.obj)
          (ModuleCat.RightExtension.tmul (RingHom.fst R S)
            (ModuleCat.prodRightMk R S M.obj N.obj m 0) 1) = m
        rw [ModuleCat.RightExtension.fromSemilinear_tmul, ModuleCat.prodRightFst_apply,
          ModuleCat.prodRightMk_apply]
        simp }
  let eS : ModuleCat.RightExtension.Obj (RingHom.snd R S)
      (ModuleCat.prodRight R S M.obj N.obj) ≃ₗ[Sᵐᵒᵖ] N :=
    { __ := ModuleCat.RightExtension.fromSemilinear (RingHom.snd R S)
        (ModuleCat.prodRightSnd R S M.obj N.obj)
      invFun := fun n => ModuleCat.RightExtension.tmul (RingHom.snd R S)
        (ModuleCat.prodRightMk R S M.obj N.obj 0 n) 1
      left_inv := by
        intro z
        change ModuleCat.RightExtension.tmul (RingHom.snd R S)
          (ModuleCat.prodRightMk R S M.obj N.obj 0
            (ModuleCat.RightExtension.fromSemilinear (RingHom.snd R S)
              (ModuleCat.prodRightSnd R S M.obj N.obj) z)) 1 = z
        obtain ⟨x, hx⟩ := ModuleCat.RightExtension.tmulOne_surjective (RingHom.snd R S)
          (fun s => ⟨(0, s), rfl⟩) z
        rw [← hx, ModuleCat.RightExtension.tmulOne_apply,
          ModuleCat.RightExtension.fromSemilinear_tmul, ModuleCat.prodRightSnd_apply]
        simp only [MulOpposite.op_one, one_smul]
        have hsupport : ModuleCat.prodRightMk R S M.obj N.obj 0 x.2 =
            MulOpposite.op ((0 : R), (1 : S)) • x := by
          simp only [ModuleCat.prodRightMk_apply, ModuleCat.prodRight_smul,
            MulOpposite.op_one, MulOpposite.op_zero, one_smul, zero_smul]
          rfl
        rw [hsupport, ModuleCat.RightExtension.smul_tmul]
        simp
      right_inv := by
        intro n
        change ModuleCat.RightExtension.fromSemilinear (RingHom.snd R S)
          (ModuleCat.prodRightSnd R S M.obj N.obj)
          (ModuleCat.RightExtension.tmul (RingHom.snd R S)
            (ModuleCat.prodRightMk R S M.obj N.obj 0 n) 1) = n
        rw [ModuleCat.RightExtension.fromSemilinear_tmul, ModuleCat.prodRightSnd_apply,
          ModuleCat.prodRightMk_apply]
        simp }
  apply (prodEquiv R S).injective
  rw [AddEquiv.apply_symm_apply, prodEquiv_of_module]
  apply Prod.ext
  · exact (of_eq_of_equiv R _
      ((ModuleCat.RightExtension.mapLinearEquiv (RingHom.fst R S)
        (ModuleCat.FiniteProjective.prodRightLinearEquiv R S M N)).trans eR)).symm
  · exact (of_eq_of_equiv S _
      ((ModuleCat.RightExtension.mapLinearEquiv (RingHom.snd R S)
        (ModuleCat.FiniteProjective.prodRightLinearEquiv R S M N)).trans eS)).symm

/-- Reassembling the two projection scalar-extension classes recovers the
source class. -/
theorem prodEquiv_symm_apply_prod_map (a : ProjectiveClass (R × S)) :
    (prodEquiv R S).symm (map (RingHom.fst R S) a, map (RingHom.snd R S) a) = a := by
  change (prodEquiv R S).symm (prodEquiv R S a) = a
  exact (prodEquiv R S).symm_apply_apply a

/-- The two projection maps recover a reassembled pair of classes. -/
theorem prod_map_prodEquiv_symm (a : ProjectiveClass R × ProjectiveClass S) :
    (map (RingHom.fst R S) ((prodEquiv R S).symm a),
      map (RingHom.snd R S) ((prodEquiv R S).symm a)) = a := by
  change prodEquiv R S ((prodEquiv R S).symm a) = a
  exact (prodEquiv R S).apply_symm_apply a

/-- Both projection scalar-extension maps together detect equality of classes. -/
theorem eq_iff_prod_map_eq (a b : ProjectiveClass (R × S)) :
    a = b ↔ map (RingHom.fst R S) a = map (RingHom.fst R S) b ∧
      map (RingHom.snd R S) a = map (RingHom.snd R S) b := by
  constructor
  · intro h
    subst b
    exact ⟨rfl, rfl⟩
  · intro h
    apply (prodEquiv R S).injective
    exact Prod.ext h.1 h.2

end Prod

end ProjectiveClass

namespace K0

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) [∀ i, Ring (Ri i)]

/-- Coordinate scalar extension defines the comparison from K₀ of a product
ring to the product of its factor K₀ groups, for an arbitrary index type. -/
noncomputable def piMap : K0 (∀ i, Ri i) →+ (∀ i, K0 (Ri i)) :=
  AddMonoidHom.pi (fun i ↦ map (Pi.evalRingHom Ri i))

/-- The product comparison evaluates at a coordinate by scalar extension. -/
@[simp]
theorem piMap_apply (x : K0 (∀ i, Ri i)) (i : ι) :
    piMap Ri x i = map (Pi.evalRingHom Ri i) x := by
  rfl

/-- Composing the product comparison with coordinate evaluation gives the
corresponding scalar-extension homomorphism. -/
theorem eval_comp_piMap (i : ι) :
    (Pi.evalAddMonoidHom (fun j ↦ K0 (Ri j)) i).comp (piMap Ri) =
      map (Pi.evalRingHom Ri i) := by
  rfl

/-- Coordinate scalar extension gives an additive equivalence from K₀ of a
finite product ring to the product of the factor K₀ groups. -/
noncomputable def piEquiv [Finite ι] : K0 (∀ i, Ri i) ≃+ (∀ i, K0 (Ri i)) :=
  AddEquiv.ofBijective
    (piMap Ri) (by
      let q (i : ι) : AddSubmonoid.LocalizationMap
          (⊤ : AddSubmonoid (ProjectiveClass (Ri i))) (K0 (Ri i)) :=
        AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass (Ri i)))
      let qPi : AddSubmonoid.LocalizationMap
          (⊤ : AddSubmonoid (∀ i, ProjectiveClass (Ri i))) (∀ i, K0 (Ri i)) :=
        { toAddHom := (AddMonoidHom.piMap (fun i ↦ ofClass (Ri i))).toAddHom
          isLocalizationMap := by
            have hfun :
                (AddMonoidHom.piMap (fun i ↦ ofClass (Ri i))).toAddHom.toFun =
                  Pi.map (fun i ↦ (q i).toFun) := by
              funext a i
              exact AddMonoidHom.piMap_apply (fun i ↦ ofClass (Ri i)) a i
            rw [hfun]
            simpa only [AddSubmonoid.pi_top] using
              (AddSubmonoid.IsLocalizationMap.pi
                (fun i ↦ (⊤ : AddSubmonoid (ProjectiveClass (Ri i))))
                (fun i ↦ (q i).isLocalizationMap)) }
      have htop :
          (⊤ : AddSubmonoid (ProjectiveClass (∀ i, Ri i))).map
              (ProjectiveClass.piEquiv Ri).toAddMonoidHom =
            (⊤ : AddSubmonoid (∀ i, ProjectiveClass (Ri i))) := by
        apply le_antisymm le_top
        intro a _
        exact AddSubmonoid.mem_map.mpr
          ⟨(ProjectiveClass.piEquiv Ri).symm a, AddSubmonoid.mem_top _,
            (ProjectiveClass.piEquiv Ri).apply_symm_apply a⟩
      let qA : AddSubmonoid.LocalizationMap
          (⊤ : AddSubmonoid (ProjectiveClass (∀ i, Ri i))) (∀ i, K0 (Ri i)) :=
        qPi.ofAddEquivOfDom (k := ProjectiveClass.piEquiv Ri) htop
      let e : K0 (∀ i, Ri i) ≃+ (∀ i, K0 (Ri i)) :=
        AddLocalization.addEquivOfQuotient qA
      have hforward : e.toAddMonoidHom = piMap Ri := by
        apply hom_ext_ofClass (∀ i, Ri i)
        intro a
        change e (ofClass (∀ i, Ri i) a) =
          fun i ↦ map (Pi.evalRingHom Ri i) (ofClass (∀ i, Ri i) a)
        change AddLocalization.addEquivOfQuotient qA
          ((AddLocalization.addMonoidOf
            (⊤ : AddSubmonoid (ProjectiveClass (∀ i, Ri i)))) a) = _
        rw [AddLocalization.addEquivOfQuotient_addMonoidOf]
        funext i
        change ofClass (Ri i) (ProjectiveClass.map (Pi.evalRingHom Ri i) a) = _
        exact (map_ofClass (Pi.evalRingHom Ri i) a).symm
      rw [← hforward]
      exact e.bijective)

variable [Finite ι]

/-- The whole K₀ forward homomorphism is the family of coordinate
scalar-extension homomorphisms. -/
theorem piEquiv_toAddMonoidHom :
    (piEquiv Ri).toAddMonoidHom =
      AddMonoidHom.pi (fun i ↦ map (Pi.evalRingHom Ri i)) := by
  rfl

/-- Composing the K₀ decomposition with coordinate evaluation gives the
coordinate scalar-extension homomorphism. -/
theorem eval_comp_piEquiv (i : ι) :
    (Pi.evalAddMonoidHom (fun j ↦ K0 (Ri j)) i).comp
        (piEquiv Ri).toAddMonoidHom = map (Pi.evalRingHom Ri i) := by
  rfl

/-- The K₀ decomposition evaluates at any coordinate by scalar extension. -/
@[simp]
theorem piEquiv_apply (z : K0 (∀ i, Ri i)) (i : ι) :
    piEquiv Ri z i = map (Pi.evalRingHom Ri i) z := by
  rfl

/-- A finite projective module in any carrier universe decomposes into the K₀
generators of its coordinate right scalar extensions. -/
@[simp]
theorem piEquiv_of_module (M : Type uM) [AddCommGroup M]
    [Module (∀ i, Ri i)ᵐᵒᵖ M]
    [Module.Finite (∀ i, Ri i)ᵐᵒᵖ M] [Module.Projective (∀ i, Ri i)ᵐᵒᵖ M]
    (i : ι) :
    piEquiv Ri (of (∀ i, Ri i) M) i =
      of (Ri i) (ModuleCat.RightExtension.Obj (Pi.evalRingHom Ri i) M) := by
  simpa only [piEquiv_apply] using map_of (Pi.evalRingHom Ri i) M

/-- The inverse K₀ decomposition of factor module generators is the generator
of their canonical finite-projective coefficient product. -/
theorem piEquiv_symm_of_module
    (Mi : ∀ i, ModuleCat.FiniteProjective.{uR, uM} (Ri i)ᵐᵒᵖ) :
    (piEquiv Ri).symm (fun i ↦ of (Ri i) (Mi i)) =
      of (∀ i, Ri i) (ModuleCat.FiniteProjective.pi Ri Mi) := by
  apply (piEquiv Ri).injective
  rw [AddEquiv.apply_symm_apply]
  funext i
  rw [piEquiv_of_module]
  exact (of_eq_of_equiv (Ri i) _
    ((ModuleCat.RightExtension.mapLinearEquiv (Pi.evalRingHom Ri i)
      (ModuleCat.FiniteProjective.piLinearEquiv Ri Mi)).trans
      (ModuleCat.RightExtension.piRecoverLinearEquiv Ri
        (fun j ↦ (Mi j).obj) i))).symm

/-- The class-to-K₀ maps commute with finite-product decomposition as whole
additive homomorphisms. -/
theorem piEquiv_comp_ofClass :
    (piEquiv Ri).toAddMonoidHom.comp (ofClass (∀ i, Ri i)) =
      (AddMonoidHom.piMap (fun i ↦ ofClass (Ri i))).comp
        (ProjectiveClass.piEquiv Ri).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro a
  funext i
  exact map_ofClass (Pi.evalRingHom Ri i) a

/-- On every class generator, decomposition commutes with group completion
in each coordinate. -/
@[simp]
theorem piEquiv_ofClass (a : ProjectiveClass (∀ i, Ri i)) (i : ι) :
    piEquiv Ri (ofClass (∀ i, Ri i) a) i =
      ofClass (Ri i) (ProjectiveClass.piEquiv Ri a i) := by
  simpa only [piEquiv_apply, ProjectiveClass.piEquiv_apply] using
    map_ofClass (Pi.evalRingHom Ri i) a

/-- The inverse K₀ decomposition of a family of class generators is the
generator of the reassembled class. -/
theorem piEquiv_symm_ofClass (a : ∀ i, ProjectiveClass (Ri i)) :
    (piEquiv Ri).symm (fun i ↦ ofClass (Ri i) (a i)) =
      ofClass (∀ i, Ri i) ((ProjectiveClass.piEquiv Ri).symm a) := by
  apply (piEquiv Ri).injective
  funext i
  simp only [AddEquiv.apply_symm_apply, piEquiv_ofClass]

/-- The inverse K₀ decomposition sends a family of differences of class
generators to the difference of the reassembled generators, without any
cancellation hypothesis on projective classes. -/
theorem piEquiv_symm_sub_ofClass (a b : ∀ i, ProjectiveClass (Ri i)) :
    (piEquiv Ri).symm (fun i ↦ ofClass (Ri i) (a i) - ofClass (Ri i) (b i)) =
      ofClass (∀ i, Ri i) ((ProjectiveClass.piEquiv Ri).symm a) -
        ofClass (∀ i, Ri i) ((ProjectiveClass.piEquiv Ri).symm b) := by
  have hsub :
      (fun i ↦ ofClass (Ri i) (a i)) - (fun i ↦ ofClass (Ri i) (b i)) =
        (fun i ↦ ofClass (Ri i) (a i) - ofClass (Ri i) (b i)) := by
    funext i
    exact Pi.sub_apply _ _ i
  simpa only [hsub, piEquiv_symm_ofClass] using
    (piEquiv Ri).symm.map_sub
      (fun i ↦ ofClass (Ri i) (a i)) (fun i ↦ ofClass (Ri i) (b i))

/-- Reassembling all coordinate scalar extensions recovers an arbitrary
source K₀ element. -/
theorem piEquiv_symm_apply_pi_map (z : K0 (∀ i, Ri i)) :
    (piEquiv Ri).symm (fun i ↦ map (Pi.evalRingHom Ri i) z) = z := by
  change (piEquiv Ri).symm (piEquiv Ri z) = z
  exact (piEquiv Ri).symm_apply_apply z

/-- All coordinate scalar extensions of a reassembled K₀ family recover the
original family. -/
theorem pi_map_piEquiv_symm (z : ∀ i, K0 (Ri i)) :
    (fun i ↦ map (Pi.evalRingHom Ri i) ((piEquiv Ri).symm z)) = z := by
  change piEquiv Ri ((piEquiv Ri).symm z) = z
  exact (piEquiv Ri).apply_symm_apply z

/-- All coordinate scalar-extension maps together detect equality of arbitrary
K₀ elements, not only module generators. -/
theorem eq_iff_pi_map_eq (z w : K0 (∀ i, Ri i)) :
    z = w ↔ ∀ i, map (Pi.evalRingHom Ri i) z = map (Pi.evalRingHom Ri i) w := by
  constructor
  · intro h
    subst w
    intro i
    rfl
  · intro h
    apply (piEquiv Ri).injective
    funext i
    exact h i

end Pi

section Prod

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]

/-- The two projection scalar extensions give the K₀ decomposition for a
binary product of rings, with independently sized factors. -/
noncomputable def prodEquiv : K0 (R × S) ≃+ (K0 R × K0 S) :=
  AddEquiv.ofBijective
    ((map (RingHom.fst R S)).prod (map (RingHom.snd R S))) (by
      let qR : AddSubmonoid.LocalizationMap
          (⊤ : AddSubmonoid (ProjectiveClass R)) (K0 R) :=
        AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass R))
      let qS : AddSubmonoid.LocalizationMap
          (⊤ : AddSubmonoid (ProjectiveClass S)) (K0 S) :=
        AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass S))
      let qRS : AddSubmonoid.LocalizationMap
          (⊤ : AddSubmonoid (ProjectiveClass R × ProjectiveClass S)) (K0 R × K0 S) :=
        { toAddHom := ((ofClass R).prodMap (ofClass S)).toAddHom
          isLocalizationMap :=
            { map_addUnits := by
                intro c
                apply Prod.isAddUnit_iff.mpr
                exact ⟨qR.map_addUnits ⟨c.1.1, AddSubmonoid.mem_top _⟩,
                  qS.map_addUnits ⟨c.1.2, AddSubmonoid.mem_top _⟩⟩
              surj := by
                intro z
                obtain ⟨x, hx⟩ := qR.surj z.1
                obtain ⟨y, hy⟩ := qS.surj z.2
                refine ⟨((x.1, y.1), ⟨(x.2, y.2), AddSubmonoid.mem_top _⟩), ?_⟩
                exact Prod.ext hx hy
              exists_of_eq := by
                intro x y h
                have hR : qR x.1 = qR y.1 := congrArg Prod.fst h
                have hS : qS x.2 = qS y.2 := congrArg Prod.snd h
                obtain ⟨cR, hcR⟩ := qR.exists_of_eq hR
                obtain ⟨cS, hcS⟩ := qS.exists_of_eq hS
                exact ⟨⟨(cR, cS), AddSubmonoid.mem_top _⟩, Prod.ext hcR hcS⟩ } }
      have htop :
          (⊤ : AddSubmonoid (ProjectiveClass (R × S))).map
              (ProjectiveClass.prodEquiv R S).toAddMonoidHom =
            (⊤ : AddSubmonoid (ProjectiveClass R × ProjectiveClass S)) := by
        apply le_antisymm le_top
        intro a _
        exact AddSubmonoid.mem_map.mpr
          ⟨(ProjectiveClass.prodEquiv R S).symm a, AddSubmonoid.mem_top _,
            (ProjectiveClass.prodEquiv R S).apply_symm_apply a⟩
      let qA : AddSubmonoid.LocalizationMap
          (⊤ : AddSubmonoid (ProjectiveClass (R × S))) (K0 R × K0 S) :=
        qRS.ofAddEquivOfDom (k := ProjectiveClass.prodEquiv R S) htop
      let e : K0 (R × S) ≃+ (K0 R × K0 S) :=
        AddLocalization.addEquivOfQuotient qA
      have hforward : e.toAddMonoidHom =
          (map (RingHom.fst R S)).prod (map (RingHom.snd R S)) := by
        apply hom_ext_ofClass (R × S)
        intro a
        change e (ofClass (R × S) a) =
          (map (RingHom.fst R S) (ofClass (R × S) a),
            map (RingHom.snd R S) (ofClass (R × S) a))
        change AddLocalization.addEquivOfQuotient qA
          ((AddLocalization.addMonoidOf
            (⊤ : AddSubmonoid (ProjectiveClass (R × S)))) a) = _
        rw [AddLocalization.addEquivOfQuotient_addMonoidOf]
        change (ofClass R (ProjectiveClass.map (RingHom.fst R S) a),
          ofClass S (ProjectiveClass.map (RingHom.snd R S) a)) = _
        exact Prod.ext (map_ofClass (RingHom.fst R S) a).symm
          (map_ofClass (RingHom.snd R S) a).symm
      rw [← hforward]
      exact e.bijective)

/-- The whole K₀ forward homomorphism is the pair of projection
scalar-extension homomorphisms. -/
theorem prodEquiv_toAddMonoidHom :
    (prodEquiv R S).toAddMonoidHom =
      (map (RingHom.fst R S)).prod (map (RingHom.snd R S)) := by
  rfl

/-- The first K₀ component homomorphism is scalar extension along `RingHom.fst`. -/
theorem fst_comp_prodEquiv :
    (AddMonoidHom.fst (K0 R) (K0 S)).comp
        (prodEquiv R S).toAddMonoidHom = map (RingHom.fst R S) := by
  rfl

/-- The second K₀ component homomorphism is scalar extension along `RingHom.snd`. -/
theorem snd_comp_prodEquiv :
    (AddMonoidHom.snd (K0 R) (K0 S)).comp
        (prodEquiv R S).toAddMonoidHom = map (RingHom.snd R S) := by
  rfl

/-- The binary K₀ decomposition evaluates by the two projection maps. -/
@[simp]
theorem prodEquiv_apply (z : K0 (R × S)) :
    prodEquiv R S z = (map (RingHom.fst R S) z, map (RingHom.snd R S) z) := by
  rfl

/-- A finite projective module in any carrier universe gives the pair of K₀
generators of its two right scalar extensions. -/
@[simp]
theorem prodEquiv_of_module (M : Type uM) [AddCommGroup M] [Module (R × S)ᵐᵒᵖ M]
    [Module.Finite (R × S)ᵐᵒᵖ M] [Module.Projective (R × S)ᵐᵒᵖ M] :
    prodEquiv R S (of (R × S) M) =
      (of R (ModuleCat.RightExtension.Obj (RingHom.fst R S) M),
        of S (ModuleCat.RightExtension.Obj (RingHom.snd R S) M)) := by
  simp only [prodEquiv_apply, map_of]

/-- The inverse binary K₀ decomposition of module generators is the generator
of their canonical right-module product, with independent carrier universes. -/
theorem prodEquiv_symm_of_module
    (M : ModuleCat.FiniteProjective.{uR, uM} Rᵐᵒᵖ)
    (N : ModuleCat.FiniteProjective.{uS, uN} Sᵐᵒᵖ) :
    (prodEquiv R S).symm (of R M, of S N) =
      of (R × S) (ModuleCat.FiniteProjective.prodRight R S M N) := by
  apply (prodEquiv R S).injective
  rw [AddEquiv.apply_symm_apply]
  change (ofClass R (ProjectiveClass.of R M), ofClass S (ProjectiveClass.of S N)) =
    prodEquiv R S (ofClass (R × S)
      (ProjectiveClass.of (R × S) (ModuleCat.FiniteProjective.prodRight R S M N)))
  rw [← ProjectiveClass.prodEquiv_symm_of_module R S M N]
  simp only [prodEquiv_apply, map_ofClass]
  change ((ofClass R).prodMap (ofClass S))
      (ProjectiveClass.of R M, ProjectiveClass.of S N) =
    ((ofClass R).prodMap (ofClass S))
      (ProjectiveClass.prodEquiv R S
        ((ProjectiveClass.prodEquiv R S).symm (ProjectiveClass.of R M, ProjectiveClass.of S N)))
  rw [AddEquiv.apply_symm_apply]

/-- The class-to-K₀ maps commute with binary-product decomposition as whole
additive homomorphisms. -/
theorem prodEquiv_comp_ofClass :
    (prodEquiv R S).toAddMonoidHom.comp (ofClass (R × S)) =
      ((ofClass R).prodMap (ofClass S)).comp
        (ProjectiveClass.prodEquiv R S).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro a
  exact Prod.ext (map_ofClass (RingHom.fst R S) a)
    (map_ofClass (RingHom.snd R S) a)

/-- Decomposition commutes with group completion on every binary-product
class generator. -/
@[simp]
theorem prodEquiv_ofClass (a : ProjectiveClass (R × S)) :
    prodEquiv R S (ofClass (R × S) a) =
      (ofClass R (ProjectiveClass.prodEquiv R S a).1,
        ofClass S (ProjectiveClass.prodEquiv R S a).2) := by
  simp only [prodEquiv_apply, ProjectiveClass.prodEquiv_apply, map_ofClass]

/-- The inverse binary K₀ decomposition of a pair of class generators is the
generator of the reassembled class. -/
theorem prodEquiv_symm_ofClass (a : ProjectiveClass R) (b : ProjectiveClass S) :
    (prodEquiv R S).symm (ofClass R a, ofClass S b) =
      ofClass (R × S) ((ProjectiveClass.prodEquiv R S).symm (a, b)) := by
  apply (prodEquiv R S).injective
  simp only [AddEquiv.apply_symm_apply, prodEquiv_ofClass]

/-- The inverse binary K₀ decomposition sends any pair of differences of class
generators to the difference of the reassembled generators. No cancellation
of projective classes is assumed. -/
theorem prodEquiv_symm_sub_ofClass
    (a a' : ProjectiveClass R) (b b' : ProjectiveClass S) :
    (prodEquiv R S).symm (ofClass R a - ofClass R a', ofClass S b - ofClass S b') =
      ofClass (R × S) ((ProjectiveClass.prodEquiv R S).symm (a, b)) -
        ofClass (R × S) ((ProjectiveClass.prodEquiv R S).symm (a', b')) := by
  simpa only [Prod.mk_sub_mk, prodEquiv_symm_ofClass] using
    (prodEquiv R S).symm.map_sub
      (ofClass R a, ofClass S b) (ofClass R a', ofClass S b')

/-- Reassembling the two projection scalar extensions recovers an arbitrary
source K₀ element. -/
theorem prodEquiv_symm_apply_prod_map (z : K0 (R × S)) :
    (prodEquiv R S).symm (map (RingHom.fst R S) z, map (RingHom.snd R S) z) = z := by
  change (prodEquiv R S).symm (prodEquiv R S z) = z
  exact (prodEquiv R S).symm_apply_apply z

/-- The two projection maps recover a reassembled pair of arbitrary K₀ elements. -/
theorem prod_map_prodEquiv_symm (z : K0 R × K0 S) :
    (map (RingHom.fst R S) ((prodEquiv R S).symm z),
      map (RingHom.snd R S) ((prodEquiv R S).symm z)) = z := by
  change prodEquiv R S ((prodEquiv R S).symm z) = z
  exact (prodEquiv R S).apply_symm_apply z

/-- Both projection scalar-extension maps together detect equality of arbitrary
K₀ elements. -/
theorem eq_iff_prod_map_eq (z w : K0 (R × S)) :
    z = w ↔ map (RingHom.fst R S) z = map (RingHom.fst R S) w ∧
      map (RingHom.snd R S) z = map (RingHom.snd R S) w := by
  constructor
  · intro h
    subst w
    exact ⟨rfl, rfl⟩
  · intro h
    apply (prodEquiv R S).injective
    exact Prod.ext h.1 h.2

end Prod

end K0

end KTheory
