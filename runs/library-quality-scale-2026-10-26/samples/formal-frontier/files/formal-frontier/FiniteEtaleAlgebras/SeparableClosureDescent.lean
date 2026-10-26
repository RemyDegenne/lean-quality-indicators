/-
Authors: Formal Frontier Agents
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FiniteEtaleAlgebras.SemilinearDescent
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Finite-stage descent inside a separable scalar extension

This file supplies the finite-data layer between an embedded finite-dimensional
subalgebra of `K ⊗[k] R` and finite-Galois semilinear descent.  The constructions
retain the literal ambient inclusions throughout.
-/

public section

open scoped TensorProduct

namespace SeparableClosureDescent

universe u v w x y

section Stage

variable {k : Type u} {L : Type v} {K : Type w} {R : Type x}
  [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K]
  [CommRing R] [Algebra k R]

/-- The literal inclusion `L ⊗[k] R → K ⊗[k] R` in a field tower. -/
@[expose] noncomputable def extensionMap : L ⊗[k] R →ₐ[L] K ⊗[k] R :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom L L K) (AlgHom.id k R)

/-- The finite-stage inclusion has its expected value on pure tensors. -/
@[simp] theorem extensionMap_tmul (l : L) (r : R) :
    extensionMap (k := k) (L := L) (K := K) (R := R) (l ⊗ₜ[k] r) =
      algebraMap L K l ⊗ₜ[k] r := rfl

/-- Extension of the coefficient field is injective inside the ambient tensor product. -/
theorem extensionMap_injective :
    Function.Injective (extensionMap (k := k) (L := L) (K := K) (R := R)) := by
  change Function.Injective (TensorProduct.map
    (IsScalarTower.toAlgHom k L K).toLinearMap (LinearMap.id : R →ₗ[k] R))
  exact TensorProduct.map_injective_of_flat_flat _ _
    (IsScalarTower.toAlgHom k L K).injective Function.injective_id

/-- The literal intersection/preimage of an embedded `K`-subalgebra with
`L ⊗[k] R`. -/
@[expose] noncomputable def stage (P : Subalgebra K (K ⊗[k] R)) : Subalgebra L (L ⊗[k] R) :=
  (P.restrictScalars L).comap
    (extensionMap (k := k) (L := L) (K := K) (R := R))

/-- Membership in the finite stage is literal ambient membership after applying
the coefficient-field inclusion. -/
@[simp] theorem mem_stage {P : Subalgebra K (K ⊗[k] R)} {z : L ⊗[k] R} :
    z ∈ stage (k := k) (L := L) P ↔
      extensionMap (k := k) (L := L) (K := K) (R := R) z ∈ P := Iff.rfl

/-- The finite-stage algebra includes into the original algebra through the
literal ambient coefficient-field map. -/
@[expose] noncomputable def stageInclusion (P : Subalgebra K (K ⊗[k] R)) :
    stage (k := k) (L := L) P →ₐ[L] P where
  toFun z := ⟨extensionMap (k := k) (L := L) (K := K) (R := R) z, z.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  commutes' l := Subtype.ext <| by
    change algebraMap L (K ⊗[k] R) l = algebraMap K (K ⊗[k] R) (algebraMap L K l)
    exact IsScalarTower.algebraMap_apply L K (K ⊗[k] R) l

/-- After coercion to the ambient tensor product, the stage inclusion is the
literal coefficient-field extension map. -/
@[simp] theorem coe_stageInclusion_apply (P : Subalgebra K (K ⊗[k] R))
    (z : stage (k := k) (L := L) P) :
    ((stageInclusion (k := k) (L := L) P z : P) : K ⊗[k] R) =
      extensionMap (k := k) (L := L) (K := K) (R := R) (z : L ⊗[k] R) := rfl

/-- Scalar extension of the finite-stage inclusion, with codomain the original
embedded subalgebra. -/
@[expose] noncomputable def reconstructionMap (P : Subalgebra K (K ⊗[k] R)) :
    K ⊗[L] stage (k := k) (L := L) P →ₐ[K] P :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom K K P)
    (stageInclusion (k := k) (L := L) P)
    (fun _ _ => .all _ _)

/-- After coercion to the ambient tensor product, reconstruction sends a pure
tensor to the scalar times the ambient finite-stage inclusion. -/
@[simp] theorem coe_reconstructionMap_tmul (P : Subalgebra K (K ⊗[k] R))
    (a : K) (z : stage (k := k) (L := L) P) :
    ((reconstructionMap (k := k) (L := L) P (a ⊗ₜ[L] z) : P) : K ⊗[k] R) =
      algebraMap K (K ⊗[k] R) a *
        extensionMap (k := k) (L := L) (K := K) (R := R) (z : L ⊗[k] R) := rfl

/-- The image of the finite stage is literally the intersection of the original
subalgebra with `L ⊗[k] R` inside the ambient `K`-tensor product. -/
theorem map_stage_eq_inf (P : Subalgebra K (K ⊗[k] R)) :
    (stage (k := k) (L := L) P).map
        (extensionMap (k := k) (L := L) (K := K) (R := R)) =
      P.restrictScalars L ⊓
        (extensionMap (k := k) (L := L) (K := K) (R := R)).range :=
  Subalgebra.map_comap_eq _ _

/-- The ambient composite of finite-stage scalar extension. -/
noncomputable def ambientReconstructionMap (P : Subalgebra K (K ⊗[k] R)) :
    K ⊗[L] stage (k := k) (L := L) P →ₐ[K] K ⊗[k] R :=
  (Algebra.TensorProduct.cancelBaseChange k L K K R).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id K K)
      (stage (k := k) (L := L) P).val)

private theorem cancelBaseChange_tmul_apply (a : K) (z : L ⊗[k] R) :
    Algebra.TensorProduct.cancelBaseChange k L K K R (a ⊗ₜ[L] z) =
      algebraMap K (K ⊗[k] R) a *
        extensionMap (k := k) (L := L) (K := K) (R := R) z := by
  induction z with
  | tmul l r =>
      simp only [Algebra.TensorProduct.cancelBaseChange_tmul, extensionMap_tmul,
        Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul]
      simp [mul_comm]
  | add x y hx hy =>
      rw [TensorProduct.tmul_add, map_add, hx, hy, map_add, mul_add]

/-- Reconstruction followed by the subtype inclusion is the literal ambient
scalar-extension map. -/
theorem ambientReconstructionMap_eq (P : Subalgebra K (K ⊗[k] R)) :
    ambientReconstructionMap (k := k) (L := L) P =
      P.val.comp (reconstructionMap (k := k) (L := L) P) := by
  apply Algebra.TensorProduct.ext'
  intro a z
  change Algebra.TensorProduct.cancelBaseChange k L K K R
      (a ⊗ₜ[L] (z : L ⊗[k] R)) = _
  exact cancelBaseChange_tmul_apply (k := k) (L := L) (K := K) (R := R) a
    (z : L ⊗[k] R)

/-- The finite-stage reconstruction map is injective, independently of whether
its image already spans the original algebra. -/
theorem reconstructionMap_injective (P : Subalgebra K (K ⊗[k] R)) :
    Function.Injective (reconstructionMap (k := k) (L := L) P) := by
  have hbase : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id K K)
        (stage (k := k) (L := L) P).val) := by
    change Function.Injective (TensorProduct.map (LinearMap.id : K →ₗ[L] K)
      (stage (k := k) (L := L) P).val.toLinearMap)
    exact TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id
      Subtype.val_injective
  have hamb : Function.Injective (ambientReconstructionMap (k := k) (L := L) P) :=
    (Algebra.TensorProduct.cancelBaseChange k L K K R).injective.comp hbase
  rw [ambientReconstructionMap_eq] at hamb
  exact fun _ _ h => hamb (congrArg P.val h)

/-- A basis whose ambient vectors are already defined over `L` makes the
finite-stage reconstruction surjective. -/
theorem reconstructionMap_surjective_of_basis {ι : Type*} [Fintype ι]
    (P : Subalgebra K (K ⊗[k] R)) (b : Module.Basis ι K P)
    (hb : ∀ i, (b i : K ⊗[k] R) ∈
      (extensionMap (k := k) (L := L) (K := K) (R := R)).range) :
    Function.Surjective (reconstructionMap (k := k) (L := L) P) := by
  classical
  let q : ι → L ⊗[k] R := fun i => Classical.choose (hb i)
  have hq (i : ι) :
      extensionMap (k := k) (L := L) (K := K) (R := R) (q i) = (b i : K ⊗[k] R) :=
    Classical.choose_spec (hb i)
  let z : ι → stage (k := k) (L := L) P := fun i => ⟨q i, by
    rw [mem_stage, hq]
    exact (b i).property⟩
  have hz (i : ι) :
      reconstructionMap (k := k) (L := L) P (1 ⊗ₜ[L] z i) = b i := by
    apply Subtype.ext
    rw [coe_reconstructionMap_tmul, hq]
    change (1 : K ⊗[k] R) * (b i : K ⊗[k] R) = (b i : K ⊗[k] R)
    exact one_mul _
  intro y
  refine ⟨∑ i, (b.repr y i) • (1 ⊗ₜ[L] z i), ?_⟩
  rw [map_sum]
  simp_rw [map_smul, hz]
  exact b.sum_repr y

/-- Literal finite-stage reconstruction as an algebra equivalence, in the
orientation from scalar extension of the intersection to the given algebra. -/
noncomputable def reconstructionEquivOfBasis {ι : Type*} [Fintype ι]
    (P : Subalgebra K (K ⊗[k] R)) (b : Module.Basis ι K P)
    (hb : ∀ i, (b i : K ⊗[k] R) ∈
      (extensionMap (k := k) (L := L) (K := K) (R := R)).range) :
    K ⊗[L] stage (k := k) (L := L) P ≃ₐ[K] P :=
  AlgEquiv.ofBijective (reconstructionMap (k := k) (L := L) P)
    ⟨reconstructionMap_injective P, reconstructionMap_surjective_of_basis P b hb⟩

/-- After coercion to the ambient tensor product, finite-stage reconstruction
is the literal scalar-extension map. -/
theorem coe_reconstructionEquivOfBasis_apply {ι : Type*} [Fintype ι]
    (P : Subalgebra K (K ⊗[k] R)) (b : Module.Basis ι K P)
    (hb : ∀ i, (b i : K ⊗[k] R) ∈
      (extensionMap (k := k) (L := L) (K := K) (R := R)).range)
    (z : K ⊗[L] stage (k := k) (L := L) P) :
    ((reconstructionEquivOfBasis P b hb z : P) : K ⊗[k] R) =
      ambientReconstructionMap (k := k) (L := L) P z := by
  rw [ambientReconstructionMap_eq]
  rfl

end Stage

section Tower

variable {k : Type u} {L : Type v} {M : Type y} {K : Type w} {R : Type x}
  [Field k] [Field L] [Field M] [Field K]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  [Algebra k K] [Algebra L K] [Algebra M K]
  [IsScalarTower k L K] [IsScalarTower k M K] [IsScalarTower L M K]
  [CommRing R] [Algebra k R]

/-- Literal coefficient-field inclusions compose in a tower. -/
theorem extensionMap_trans (z : L ⊗[k] R) :
    extensionMap (k := k) (L := L) (K := K) (R := R) z =
      extensionMap (k := k) (L := M) (K := K) (R := R)
        (extensionMap (k := k) (L := L) (K := M) (R := R) z) := by
  induction z with
  | tmul l r =>
      simp only [extensionMap_tmul]
      rw [IsScalarTower.algebraMap_apply L M K]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Taking the literal finite-stage intersection is coherent under enlargement
of the coefficient field. -/
theorem stage_tower (P : Subalgebra K (K ⊗[k] R)) :
    stage (k := k) (L := L) P =
      stage (k := k) (L := L) (stage (k := k) (L := M) P) := by
  ext z
  change extensionMap (k := k) (L := L) (K := K) (R := R) z ∈ P ↔
    extensionMap (k := k) (L := M) (K := K) (R := R)
      (extensionMap (k := k) (L := L) (K := M) (R := R) z) ∈ P
  rw [extensionMap_trans (M := M)]

end Tower

section ReconstructionTower

variable {k : Type u} {L : Type v} {K : Type w} {R : Type x}
  [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K]
  [CommRing R] [Algebra k R]

/-- Compose literal reconstruction over a finite coefficient field with the
coefficient-field tower equivalence. -/
noncomputable def reconstructionEquivTrans (D : Subalgebra k R)
    (PL : Subalgebra L (L ⊗[k] R)) (P : Subalgebra K (K ⊗[k] R))
    (eFinite : L ⊗[k] D ≃ₐ[L] PL) (eStage : K ⊗[L] PL ≃ₐ[K] P) :
    K ⊗[k] D ≃ₐ[K] P :=
  (Algebra.TensorProduct.cancelBaseChange k L K K D).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) eFinite).trans eStage)

/-- The composite tower reconstruction retains the literal ambient inclusion. -/
theorem coe_reconstructionEquivTrans_apply (D : Subalgebra k R)
    (PL : Subalgebra L (L ⊗[k] R)) (P : Subalgebra K (K ⊗[k] R))
    (eFinite : L ⊗[k] D ≃ₐ[L] PL) (eStage : K ⊗[L] PL ≃ₐ[K] P)
    (hFinite : ∀ z, ((eFinite z : PL) : L ⊗[k] R) =
      Algebra.TensorProduct.map (AlgHom.id L L) D.val z)
    (hStage : ∀ z, ((eStage z : P) : K ⊗[k] R) =
      Algebra.TensorProduct.cancelBaseChange k L K K R
        (Algebra.TensorProduct.map (AlgHom.id K K) PL.val z))
    (z : K ⊗[k] D) :
    (((reconstructionEquivTrans D PL P eFinite eStage) z : P) : K ⊗[k] R) =
      Algebra.TensorProduct.map (AlgHom.id K K) D.val z := by
  induction z with
  | tmul a d =>
      change ((eStage (a ⊗ₜ[L] eFinite (1 ⊗ₜ[k] d)) : P) : K ⊗[k] R) = _
      rw [hStage]
      change Algebra.TensorProduct.cancelBaseChange k L K K R
          (a ⊗ₜ[L] ((eFinite (1 ⊗ₜ[k] d) : PL) : L ⊗[k] R)) = _
      rw [hFinite]
      change Algebra.TensorProduct.cancelBaseChange k L K K R
          (a ⊗ₜ[L] (1 ⊗ₜ[k] (d : R))) = _
      rw [Algebra.TensorProduct.cancelBaseChange_tmul]
      simp
  | add a b ha hb =>
      simp only [map_add]
      change (((reconstructionEquivTrans D PL P eFinite eStage) a : P) :
          K ⊗[k] R) +
        (((reconstructionEquivTrans D PL P eFinite eStage) b : P) :
          K ⊗[k] R) = _
      rw [ha, hb]

end ReconstructionTower

section Capture

variable {k : Type u} {K : Type w} {R : Type x}
  [Field k] [Field K] [Algebra k K] [IsGalois k K]
  [CommRing R] [Algebra k R]

omit [IsGalois k K] in
private theorem extensionMap_map_inclusion
    (L : FiniteGaloisIntermediateField k K) (M : Submodule k K)
    (hM : M ≤ L.toIntermediateField.toSubalgebra.toSubmodule) (z : M ⊗[k] R) :
    extensionMap (k := k) (L := L) (K := K) (R := R)
        (TensorProduct.map (Submodule.inclusion hM) (LinearMap.id : R →ₗ[k] R) z) =
      M.subtype.rTensor R z := by
  induction z with
  | tmul m r => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Finitely many basis tensors are simultaneously defined over one finite
Galois intermediate field.  This is the finite-coefficient input needed for
literal subalgebra descent. -/
theorem exists_finiteGalois_stage_basis (P : Subalgebra K (K ⊗[k] R))
    [Module.Finite K P] :
    ∃ L : FiniteGaloisIntermediateField k K,
      ∀ i : Fin (Module.finrank K P),
        (Module.finBasis K P i : K ⊗[k] R) ∈
          (extensionMap (k := k) (L := L) (K := K) (R := R)).range := by
  classical
  let b := Module.finBasis K P
  let s : Set (K ⊗[k] R) := Set.range fun i : Fin (Module.finrank K P) =>
    (b i : K ⊗[k] R)
  obtain ⟨M, hMfin, hsM⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite s (Set.finite_range _)
  have hMfg : M.FG := Module.Finite.iff_fg.mp hMfin
  obtain ⟨S, hSfin, hSspan⟩ := Submodule.fg_def.mp hMfg
  let _ : Finite S := hSfin
  let L := FiniteGaloisIntermediateField.adjoin k S
  have hML : M ≤ L.toIntermediateField.toSubalgebra.toSubmodule := by
    rw [← hSspan]
    exact Submodule.span_le.mpr (FiniteGaloisIntermediateField.subset_adjoin k S)
  refine ⟨L, fun i => ?_⟩
  have hi : (b i : K ⊗[k] R) ∈ s := ⟨i, rfl⟩
  obtain ⟨z, hz⟩ := hsM hi
  refine ⟨TensorProduct.map (Submodule.inclusion hML) (LinearMap.id : R →ₗ[k] R) z, ?_⟩
  change extensionMap (k := k) (L := L) (K := K) (R := R)
    (TensorProduct.map (Submodule.inclusion hML) (LinearMap.id : R →ₗ[k] R) z) = _
  rw [extensionMap_map_inclusion]
  exact hz

end Capture

section Stability


variable {k : Type u} {K : Type w} {R : Type x}
  [Field k] [Field K] [Algebra k K] [IsGalois k K]
  [CommRing R] [Algebra k R]

omit [IsGalois k K] in
/-- Coefficientwise conjugation commutes with the literal inclusion from a
finite normal intermediate field. -/
theorem extensionMap_coefficientwise
    (L : FiniteGaloisIntermediateField k K) (sigma : K ≃ₐ[k] K)
    (z : L ⊗[k] R) :
    extensionMap (k := k) (L := L) (K := K) (R := R)
        (GaloisDescent.coefficientwise (R := R)
          (AlgEquiv.restrictNormalHom L.toIntermediateField sigma) z) =
      GaloisDescent.coefficientwise (R := R) sigma
        (extensionMap (k := k) (L := L) (K := K) (R := R) z) := by
  induction z with
  | tmul l r =>
      change algebraMap L K
          ((AlgEquiv.restrictNormalHom L.toIntermediateField sigma) l) ⊗ₜ[k] r =
        sigma (algebraMap L K l) ⊗ₜ[k] r
      congr 1
      exact AlgEquiv.restrictNormal_commutes sigma L.toIntermediateField l
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Absolute coefficientwise stability passes to the literal finite-stage
intersection.  Surjectivity of restriction supplies a lift of each finite-level
automorphism; the result is independent of that choice because the ambient map
only sees its restriction. -/
theorem stage_isStable (L : FiniteGaloisIntermediateField k K)
    (P : Subalgebra K (K ⊗[k] R)) (hP : GaloisDescent.IsStable P) :
    GaloisDescent.IsStable (stage (k := k) (L := L) P) := by
  intro tau z hz
  obtain ⟨sigma, hsigma⟩ := AlgEquiv.restrictNormalHom_surjective K tau
  rw [mem_stage]
  rw [← hsigma, extensionMap_coefficientwise]
  exact hP sigma hz

end Stability

section FiniteStage

variable {k : Type u} {K : Type w} {R : Type x}
  [Field k] [Field K] [Algebra k K] [IsGalois k K]
  [CommRing R] [Algebra k R]

/-- A finite-etale, absolutely stable embedded algebra is reconstructed from a
stable finite-etale algebra over one finite Galois intermediate field.  Both
equivalences and the stage itself use the literal ambient inclusions. -/
theorem exists_finiteGalois_stage (P : Subalgebra K (K ⊗[k] R))
    (hP : GaloisDescent.IsStable P) (hEtale : P.IsFiniteEtale) :
    ∃ L : FiniteGaloisIntermediateField k K,
      GaloisDescent.IsStable (stage (k := k) (L := L) P) ∧
      (stage (k := k) (L := L) P).IsFiniteEtale ∧
      ∃ e : K ⊗[L] stage (k := k) (L := L) P ≃ₐ[K] P,
        ∀ z, ((e z : P) : K ⊗[k] R) =
          ambientReconstructionMap (k := k) (L := L) P z := by
  let : Module.Finite K P := hEtale.1
  obtain ⟨L, hb⟩ := exists_finiteGalois_stage_basis P
  let e := reconstructionEquivOfBasis P (Module.finBasis K P) hb
  have hstage : GaloisDescent.IsStable (stage (k := k) (L := L) P) :=
    stage_isStable L P hP
  have hstageEtale : (stage (k := k) (L := L) P).IsFiniteEtale := by
    let : Algebra.Etale K P := hEtale.2
    let : Module.Finite K (K ⊗[L] stage (k := k) (L := L) P) :=
      (Module.Finite.equiv_iff e.toLinearEquiv).2 inferInstance
    let : Algebra.Etale K (K ⊗[L] stage (k := k) (L := L) P) :=
      Algebra.Etale.of_equiv e.symm
    exact ⟨Module.Finite.of_finite_tensorProduct_of_faithfullyFlat K,
      Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat K⟩
  exact ⟨L, hstage, hstageEtale, e,
    coe_reconstructionEquivOfBasis_apply P (Module.finBasis K P) hb⟩

/-- The literal scalar-extension inclusion of a `k`-subalgebra into
`K ⊗[k] R`. -/
@[expose] noncomputable def scalarExtensionMap (D : Subalgebra k R) :
    K ⊗[k] D →ₐ[K] K ⊗[k] R :=
  Algebra.TensorProduct.map (AlgHom.id K K) D.val

omit [IsGalois k K] in
/-- The literal scalar-extension inclusion sends `a ⊗ d` to `a ⊗ (d : R)`. -/
@[simp] theorem scalarExtensionMap_tmul (D : Subalgebra k R) (a : K) (d : D) :
    scalarExtensionMap (K := K) D (a ⊗ₜ[k] d) = a ⊗ₜ[k] (d : R) := rfl

/-- The literal scalar-extension inclusion is injective. -/
theorem scalarExtensionMap_injective (D : Subalgebra k R) :
    Function.Injective (scalarExtensionMap (K := K) D) := by
  change Function.Injective (D.val.toLinearMap.baseChange K)
  exact Module.Flat.lTensor_preserves_injective_linearMap D.val.toLinearMap
    Subtype.val_injective

end FiniteStage

section Package

variable {k : Type u} {K : Type w} {R : Type x}
  [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
  [CommRing R] [Algebra k R]

/-- The complete literal output of separable-closure descent. -/
structure Package (P : Subalgebra K (K ⊗[k] R)) where
  /-- The reconstructed algebra in the original ambient algebra. -/
  algebra : Subalgebra k R
  /-- The reconstructed subalgebra is finite etale over `k`. -/
  isFiniteEtale : algebra.IsFiniteEtale
  /-- Canonical orientation from scalar extension to the given subalgebra. -/
  reconstruction : K ⊗[k] algebra ≃ₐ[K] P
  /-- Reconstruction is the literal ambient scalar-extension inclusion. -/
  coe_reconstruction (z : K ⊗[k] algebra) :
    ((reconstruction z : P) : K ⊗[k] R) = scalarExtensionMap algebra z
  /-- The descended algebra is the honest preimage in `R`. -/
  mem_algebra (r : R) :
    r ∈ algebra ↔ (Algebra.TensorProduct.includeRight r : K ⊗[k] R) ∈ P

omit [IsSepClosure k K] in
/-- An ambient-compatible reconstruction equivalence identifies the literal
range of scalar extension with the given subalgebra. -/
theorem scalarExtensionMap_range_of_equiv
    (P : Subalgebra K (K ⊗[k] R)) (D : Subalgebra k R)
    (e : K ⊗[k] D ≃ₐ[K] P)
    (he : ∀ z, ((e z : P) : K ⊗[k] R) = scalarExtensionMap D z) :
    (scalarExtensionMap D).range = P := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change scalarExtensionMap D z ∈ P
    rw [← he z]
    exact (e z).property
  · intro hx
    refine ⟨e.symm ⟨x, hx⟩, ?_⟩
    change scalarExtensionMap D (e.symm ⟨x, hx⟩) = x
    rw [← he]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)

/-- A finite-etale subalgebra embedded after extension to a separable closure,
and stable under every coefficientwise absolute-Galois automorphism, descends
to an honest finite-etale subalgebra of the original ambient algebra. -/
noncomputable def package (P : Subalgebra K (K ⊗[k] R))
    (hP : GaloisDescent.IsStable P) (hEtale : P.IsFiniteEtale) : Package P := by
  classical
  let hex := exists_finiteGalois_stage P hP hEtale
  let L := Classical.choose hex
  have hL := Classical.choose_spec hex
  let hstable := hL.1
  let hstageEtale := hL.2.1
  let eStage := Classical.choose hL.2.2
  have heStage := Classical.choose_spec hL.2.2
  let PL := stage (k := k) (L := L) P
  let D := GaloisDescent.descended PL
  let eFinite := GaloisDescent.reconstructionEquiv PL hstable
  let e : K ⊗[k] D ≃ₐ[K] P := reconstructionEquivTrans D PL P eFinite eStage
  have hD : D.IsFiniteEtale :=
    GaloisDescent.descended_isFiniteEtale PL hstable hstageEtale
  have he (z : K ⊗[k] D) :
      ((e z : P) : K ⊗[k] R) = scalarExtensionMap D z := by
    exact coe_reconstructionEquivTrans_apply D PL P eFinite eStage
      (GaloisDescent.coe_reconstructionEquiv_apply PL hstable) heStage z
  refine
    { algebra := D
      isFiniteEtale := hD
      reconstruction := e
      coe_reconstruction := he
      mem_algebra := fun r => ?_ }
  change r ∈ GaloisDescent.descended PL ↔ _
  rw [GaloisDescent.mem_descended]
  change (1 ⊗ₜ[k] r : L ⊗[k] R) ∈ PL ↔ _
  rw [mem_stage]
  change (algebraMap L K 1 ⊗ₜ[k] r : K ⊗[k] R) ∈ P ↔ _
  simp only [map_one]
  rfl

/-- The separable-closure reconstruction has literal ambient range equal to the
original stable subalgebra. -/
theorem package_range (P : Subalgebra K (K ⊗[k] R))
    (hP : GaloisDescent.IsStable P) (hEtale : P.IsFiniteEtale) :
    (scalarExtensionMap (package P hP hEtale).algebra).range = P :=
  scalarExtensionMap_range_of_equiv P _ (package P hP hEtale).reconstruction
    (package P hP hEtale).coe_reconstruction

end Package

end SeparableClosureDescent
