/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.TensorCoefficients
public import SimplicialObjects.TensorCoefficientMaps
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.Logic.Equiv.Set

/-!
# Homology of terminal simplicial sets

For every `A : Type a` with `[AddCommGroup A]` and every terminal `T : SSet.{w}`,
write `K = SSet.tensorNormalizedChainComplex.{a,w,p} A T` and
`C = ModuleCat.of ℤ (ULift.{max w p} A) : ModuleCat.{max a w p} ℤ`.
The coefficient, simplex and padding universes `a`, `w`, `p` are independent.
The coefficient lift in `C` is distinct from the raw degree carrier
`ULift.{max a w p} ((T.nonDegenerate n →₀ ℤ) ⊗[ℤ] A)`. The complex `K` retains
its original tensor carriers, canonical integer-module structures and independently
defined alternating differential.

## Main API

* `SSet.tensorNormalizedHomologyZeroIsoCoefficient` identifies `H₀(K)` with `C`.
  Its hom and inverse are the two comparison morphisms below; the projection
  lemmas expose their class and naturality APIs without unfolding coordinates.
* `SSet.tensorNormalizedHomologyZeroToCoefficient` is the comparison
  `φ : H₀(K) ⟶ C`, descending degree-zero coordinate evaluation through opcycles.
  `SSet.tensorNormalizedCoefficientToHomologyZero` is `β : C ⟶ H₀(K)`, inserting
  the unique vertex coordinate and taking its class through cycles and homology.
  The laws `SSet.tensorNormalizedHomologyZeroToCoefficient_comp_fromCoefficient`
  and `SSet.tensorNormalizedCoefficientToHomologyZero_comp_toCoefficient` give
  `φ ≫ β = 𝟙` and `β ≫ φ = 𝟙`, respectively.
* `SSet.tensorNormalizedHomologyZeroToCoefficient_class` sends the homology class
  of every vertex tensor `[v] ⊗ x` to `ULift.up x`.
  `SSet.tensorNormalizedCoefficientToHomologyZero_up` recovers the same class
  from `ULift.up x`, using the degree-zero cycles isomorphism.
* `SSet.tensorNormalizedHomologyZeroToCoefficient_coefficient_naturality` commutes
  with every additive homomorphism `g : A →+ B`, with independent coefficient
  universes `a`, `b`, source padding `max b p` and target padding `max a p`.
  The lifted coefficient arrow sends `ULift.up x` to `ULift.up (g x)`.
  `SSet.tensorNormalizedHomologyZeroToCoefficient_naturality` commutes with every
  simplicial map between terminal simplicial sets.
* `SSet.isZero_tensorNormalizedHomology_succ` gives `Hₙ₊₁(K) = 0` for every `n : ℕ`.
  More generally, `SSet.isZero_tensorNormalizedHomology_of_hasDimensionLT` gives
  zero tensor homology for any `S : SSet.{w}` with `S.HasDimensionLT d` in every
  degree `n ≥ d`.

## Limitations

These statements concern simplicial normalized chains and nonnegatively indexed
ordinary homology only. They do not give a `TopCat` or singular-chain comparison,
reduced or relative homology, a long exact sequence, or all results of the cited
sections of May's book, and make no source-wide coverage claim.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, revised author edition,
  §13.1 and §16.4: point homology and normalized chains. The statements here are
  their simplicial normalized-chain counterparts.
* Mathlib supplies categorical homology, cycles, opcycles, homology projection
  maps, normalized-chain dimension bounds, terminal-object transport and
  `Finsupp.uniqueLinearEquiv`.
* `SimplicialObjects.TensorCoefficients` supplies the integral tensor complex,
  its normalized-chain comparison and Finsupp coordinates;
  `SimplicialObjects.TensorCoefficientMaps` supplies coefficient change and
  its generator formulas.
-/

public section

universe a b w p

open CategoryTheory Limits Opposite
open scoped Simplicial TensorProduct

namespace SSet

/-- A terminal simplicial set has a unique nondegenerate vertex. -/
@[instance_reducible]
private noncomputable def terminalNonDegenerateZeroUnique
    (T : SSet.{w}) (hT : IsTerminal T) : Unique (T.nonDegenerate 0) := by
  let h₀ : IsTerminal (T.obj (op ⦋0⦌)) :=
    IsTerminal.isTerminalObj
      ((evaluation SimplexCategoryᵒᵖ (Type w)).obj (op ⦋0⦌)) T hT
  letI : Unique (T.obj (op ⦋0⦌)) := Types.isTerminalEquivUnique _ h₀
  exact ((Set.equivOfEq (T.nondegenerate_zero)).trans (Equiv.Set.univ _)).unique

/-- The degree-one differential of the tensor complex of a terminal simplicial
set is zero. -/
private theorem tensorNormalizedTerminal_d_one_zero
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T) :
    (tensorNormalizedChainComplex.{a, w, p} A T).d 1 0 = 0 := by
  let : T.HasDimensionLT 1 :=
    (hasDimensionLT_iff_of_iso
      (hT.uniqueUpToIso stdSimplex.isTerminalObj₀.{w}) 1).2
        (inferInstance : (Δ[0] : SSet.{w}).HasDimensionLT 1)
  have hN : IsZero
      ((T.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).X 1) :=
    T.isZero_normalizedChainComplex_X_of_hasDimensionLT
      (ModuleCat.of ℤ (ULift.{max w p} A)) 1 1 (Nat.le_refl 1)
  have hK : IsZero ((tensorNormalizedChainComplex.{a, w, p} A T).X 1) :=
    hN.of_iso (HomologicalComplex.Hom.isoApp (tensorNormalizedChainIso.{a, w, p} A T) 1)
  exact hK.eq_of_src _ _

private noncomputable def tensorNormalizedZeroIsoCoefficient
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T) :
    (tensorNormalizedChainComplex.{a, w, p} A T).X 0 ≅
      ModuleCat.of ℤ (ULift.{max w p} A) := by
  letI : Unique (T.nonDegenerate 0) := terminalNonDegenerateZeroUnique T hT
  exact tensorNormalizedChainComplexXIsoFinsupp.{a, w, p} A T 0 ≪≫
    (Finsupp.uniqueLinearEquiv ℤ (ULift.{max w p} A)
      (default : T.nonDegenerate 0)).toModuleIso

/-- The morphism from degree-zero homology of terminal normalized tensor chains
obtained by descending the fixed degree-zero coefficient coordinates through
Mathlib's opcycles. -/
noncomputable def tensorNormalizedHomologyZeroToCoefficient
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T) :
    (tensorNormalizedChainComplex.{a, w, p} A T).homology 0 ⟶
      ModuleCat.of ℤ (ULift.{max w p} A) := by
  exact (tensorNormalizedChainComplex.{a, w, p} A T).homologyι 0 ≫
    (tensorNormalizedChainComplex.{a, w, p} A T).descOpcycles (i := 0)
      (tensorNormalizedZeroIsoCoefficient.{a, w, p} A T hT).hom 1 (by simp) (by
        rw [tensorNormalizedTerminal_d_one_zero.{a, w, p} A T hT, zero_comp])

/-- The morphism taking a lifted coefficient to degree-zero homology of terminal
normalized tensor chains, using inverse degree-zero coordinates followed by
Mathlib's cycles isomorphism and homology projection. -/
noncomputable def tensorNormalizedCoefficientToHomologyZero
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T) :
    ModuleCat.of ℤ (ULift.{max w p} A) ⟶
      (tensorNormalizedChainComplex.{a, w, p} A T).homology 0 := by
  exact (tensorNormalizedZeroIsoCoefficient.{a, w, p} A T hT).inv ≫
    (ChainComplex.cycles₀Iso (tensorNormalizedChainComplex.{a, w, p} A T)).inv ≫
      (tensorNormalizedChainComplex.{a, w, p} A T).homologyπ 0

/-- The coefficient comparison followed by the vertex-class comparison is the
identity on degree-zero homology. -/
theorem tensorNormalizedHomologyZeroToCoefficient_comp_fromCoefficient
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T) :
    tensorNormalizedHomologyZeroToCoefficient.{a, w, p} A T hT ≫
        tensorNormalizedCoefficientToHomologyZero.{a, w, p} A T hT =
      𝟙 ((tensorNormalizedChainComplex.{a, w, p} A T).homology 0) := by
  -- It suffices to check the homology classes of cycles.
  rw [← cancel_epi ((tensorNormalizedChainComplex.{a, w, p} A T).homologyπ 0)]
  simp only [tensorNormalizedHomologyZeroToCoefficient,
    tensorNormalizedCoefficientToHomologyZero, Category.assoc,
    HomologicalComplex.homology_π_ι_assoc, HomologicalComplex.p_descOpcycles_assoc,
    Iso.hom_inv_id_assoc, HomologicalComplex.iCyclesIso_hom_inv_id_assoc,
    Category.comp_id]

/-- The vertex-class comparison followed by the coefficient comparison is the
identity on the specified lifted coefficient object. -/
theorem tensorNormalizedCoefficientToHomologyZero_comp_toCoefficient
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T) :
    tensorNormalizedCoefficientToHomologyZero.{a, w, p} A T hT ≫
        tensorNormalizedHomologyZeroToCoefficient.{a, w, p} A T hT =
      𝟙 (ModuleCat.of ℤ (ULift.{max w p} A) : ModuleCat.{max a w p} ℤ) := by
  simp only [tensorNormalizedCoefficientToHomologyZero,
    tensorNormalizedHomologyZeroToCoefficient, Category.assoc,
    HomologicalComplex.homology_π_ι_assoc, HomologicalComplex.p_descOpcycles,
    HomologicalComplex.iCyclesIso_inv_hom_id_assoc, Iso.inv_hom_id]

/-- Degree-zero homology of a terminal simplicial set with abelian coefficients.

The hom and inverse are coefficient evaluation and vertex-class insertion. This
is the simplicial normalized-chain counterpart of the point dimension statement
in May, *A Concise Course in Algebraic Topology*, revised author edition, §13.1,
using the normalized integral tensor construction of §16.4. -/
@[expose]
noncomputable def tensorNormalizedHomologyZeroIsoCoefficient
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T) :
    (tensorNormalizedChainComplex.{a, w, p} A T).homology 0 ≅
      ModuleCat.of ℤ (ULift.{max w p} A) where
  hom := tensorNormalizedHomologyZeroToCoefficient.{a, w, p} A T hT
  inv := tensorNormalizedCoefficientToHomologyZero.{a, w, p} A T hT
  hom_inv_id := tensorNormalizedHomologyZeroToCoefficient_comp_fromCoefficient.{a, w, p}
    A T hT
  inv_hom_id := tensorNormalizedCoefficientToHomologyZero_comp_toCoefficient.{a, w, p}
    A T hT

@[simp]
theorem tensorNormalizedHomologyZeroIsoCoefficient_hom
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T) :
    (tensorNormalizedHomologyZeroIsoCoefficient.{a, w, p} A T hT).hom =
      tensorNormalizedHomologyZeroToCoefficient.{a, w, p} A T hT := rfl

@[simp]
theorem tensorNormalizedHomologyZeroIsoCoefficient_inv
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T) :
    (tensorNormalizedHomologyZeroIsoCoefficient.{a, w, p} A T hT).inv =
      tensorNormalizedCoefficientToHomologyZero.{a, w, p} A T hT := rfl

private theorem tensorNormalizedZeroIsoCoefficient_hom_single
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T)
    (v : T.nonDegenerate 0) (x : A) :
    (tensorNormalizedZeroIsoCoefficient.{a, w, p} A T hT).hom
        (ULift.up (Finsupp.single v 1 ⊗ₜ[ℤ] x) :
          ULift.{max a w p} ((T.nonDegenerate 0 →₀ ℤ) ⊗[ℤ] A)) =
      (ULift.up x : ULift.{max w p} A) := by
  classical
  let : Unique (T.nonDegenerate 0) := terminalNonDegenerateZeroUnique T hT
  change (Finsupp.uniqueLinearEquiv ℤ (ULift.{max w p} A)
      (default : T.nonDegenerate 0))
    ((tensorNormalizedChainComplexXIsoFinsupp.{a, w, p} A T 0).hom
      (ULift.up (Finsupp.single v 1 ⊗ₜ[ℤ] x))) = _
  rw [tensorNormalizedChainComplexXIsoFinsupp_hom_single,
    Finsupp.uniqueLinearEquiv_apply,
    (Subsingleton.elim (default : T.nonDegenerate 0) v), Finsupp.single_eq_same]

private theorem tensorNormalizedZeroIsoCoefficient_inv_up
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T)
    (v : T.nonDegenerate 0) (x : A) :
    (tensorNormalizedZeroIsoCoefficient.{a, w, p} A T hT).inv
        (ULift.up x : ULift.{max w p} A) =
      (ULift.up (Finsupp.single v 1 ⊗ₜ[ℤ] x) :
        ULift.{max a w p} ((T.nonDegenerate 0 →₀ ℤ) ⊗[ℤ] A)) := by
  rw [← tensorNormalizedZeroIsoCoefficient_hom_single.{a, w, p} A T hT v x]
  exact ModuleCat.inv_hom_apply _ _

private theorem tensorNormalizedHomologyZeroToCoefficient_cycles₀Iso_inv
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T) :
    (ChainComplex.cycles₀Iso (tensorNormalizedChainComplex.{a, w, p} A T)).inv ≫
        (tensorNormalizedChainComplex.{a, w, p} A T).homologyπ 0 ≫
          tensorNormalizedHomologyZeroToCoefficient.{a, w, p} A T hT =
      (tensorNormalizedZeroIsoCoefficient.{a, w, p} A T hT).hom := by
  simp only [tensorNormalizedHomologyZeroToCoefficient,
    HomologicalComplex.homology_π_ι_assoc, HomologicalComplex.p_descOpcycles,
    HomologicalComplex.iCyclesIso_inv_hom_id_assoc]

/-- The original vertex tensor with coefficient `x` has coefficient `ULift.up x`
under the degree-zero homology comparison. The formula holds for every vertex
of the terminal simplicial set. -/
theorem tensorNormalizedHomologyZeroToCoefficient_class
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T)
    (v : T.nonDegenerate 0) (x : A) :
    tensorNormalizedHomologyZeroToCoefficient.{a, w, p} A T hT
        ((tensorNormalizedChainComplex.{a, w, p} A T).homologyπ 0
          ((ChainComplex.cycles₀Iso (tensorNormalizedChainComplex.{a, w, p} A T)).inv
            (ULift.up (Finsupp.single v 1 ⊗ₜ[ℤ] x) :
              ULift.{max a w p} ((T.nonDegenerate 0 →₀ ℤ) ⊗[ℤ] A)))) =
      (ULift.up x : ULift.{max w p} A) := by
  change ((ChainComplex.cycles₀Iso
      (tensorNormalizedChainComplex.{a, w, p} A T)).inv ≫
    (tensorNormalizedChainComplex.{a, w, p} A T).homologyπ 0 ≫
      tensorNormalizedHomologyZeroToCoefficient.{a, w, p} A T hT)
        (ULift.up (Finsupp.single v 1 ⊗ₜ[ℤ] x)) = _
  rw [tensorNormalizedHomologyZeroToCoefficient_cycles₀Iso_inv,
    tensorNormalizedZeroIsoCoefficient_hom_single]

/-- The lifted coefficient `x` gives the homology class of its original vertex
tensor, using the degree-zero cycles isomorphism. -/
theorem tensorNormalizedCoefficientToHomologyZero_up
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T)
    (v : T.nonDegenerate 0) (x : A) :
    tensorNormalizedCoefficientToHomologyZero.{a, w, p} A T hT
        (ULift.up x : ULift.{max w p} A) =
      (tensorNormalizedChainComplex.{a, w, p} A T).homologyπ 0
        ((ChainComplex.cycles₀Iso (tensorNormalizedChainComplex.{a, w, p} A T)).inv
          (ULift.up (Finsupp.single v 1 ⊗ₜ[ℤ] x) :
            ULift.{max a w p} ((T.nonDegenerate 0 →₀ ℤ) ⊗[ℤ] A))) := by
  change (tensorNormalizedChainComplex.{a, w, p} A T).homologyπ 0
    ((ChainComplex.cycles₀Iso (tensorNormalizedChainComplex.{a, w, p} A T)).inv
      ((tensorNormalizedZeroIsoCoefficient.{a, w, p} A T hT).inv
        (ULift.up x : ULift.{max w p} A))) = _
  rw [tensorNormalizedZeroIsoCoefficient_inv_up.{a, w, p} A T hT v x]

/-- The degree-zero comparison is natural in an arbitrary additive coefficient
homomorphism, with independent coefficient universes and balanced padding.
The coefficient arrow is `up x ↦ up (g x)`.

The homology projection and the degree-zero cycles isomorphism reduce the square
to the original vertex tensors. The chain coefficient map changes only their
coefficients, so the vertex-class formula proves the square. -/
theorem tensorNormalizedHomologyZeroToCoefficient_coefficient_naturality
    (A : Type a) (B : Type b) [AddCommGroup A] [AddCommGroup B]
    (T : SSet.{w}) (hT : IsTerminal T) (g : A →+ B) :
    HomologicalComplex.homologyMap
        (tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g T) 0 ≫
        tensorNormalizedHomologyZeroToCoefficient.{b, w, max a p} B T hT =
      tensorNormalizedHomologyZeroToCoefficient.{a, w, max b p} A T hT ≫
        ModuleCat.ofHom
          ((ULift.moduleEquiv (R := ℤ) :
              ULift.{max a w p} B ≃ₗ[ℤ] B).symm.toLinearMap ∘ₗ
            g.toIntLinearMap ∘ₗ
              (ULift.moduleEquiv (R := ℤ) :
                ULift.{max b w p} A ≃ₗ[ℤ] A).toLinearMap) := by
  let KA := tensorNormalizedChainComplex.{a, w, max b p} A T
  let KB := tensorNormalizedChainComplex.{b, w, max a p} B T
  let f : KA ⟶ KB := tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g T
  have hcycles :
      (ChainComplex.cycles₀Iso KA).inv ≫ HomologicalComplex.cyclesMap f 0 =
        f.f 0 ≫ (ChainComplex.cycles₀Iso KB).inv := by
    apply (cancel_mono (KB.iCycles 0)).mp
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.iCyclesIso_inv_hom_id,
      HomologicalComplex.iCyclesIso_inv_hom_id_assoc, Category.comp_id]
  apply (cancel_epi (KA.homologyπ 0)).mp
  apply (cancel_epi (ChainComplex.cycles₀Iso KA).inv).mp
  simp only [HomologicalComplex.homologyπ_naturality_assoc]
  rw [← Category.assoc, hcycles]
  apply tensorNormalizedChainComplex_hom_ext.{a, w, max b p} A T 0
  intro v x
  change tensorNormalizedHomologyZeroToCoefficient.{b, w, max a p} B T hT
      (KB.homologyπ 0 ((ChainComplex.cycles₀Iso KB).inv
        ((tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g T).f 0
          (ULift.up (Finsupp.single v 1 ⊗ₜ[ℤ] x) :
            ULift.{max a b w p} ((T.nonDegenerate 0 →₀ ℤ) ⊗[ℤ] A))))) =
    (ULift.up (g (tensorNormalizedHomologyZeroToCoefficient.{a, w, max b p} A T hT
      (KA.homologyπ 0 ((ChainComplex.cycles₀Iso KA).inv
        (ULift.up (Finsupp.single v 1 ⊗ₜ[ℤ] x) :
          ULift.{max a b w p} ((T.nonDegenerate 0 →₀ ℤ) ⊗[ℤ] A))))).down) :
      ULift.{max a w p} B)
  have hf := tensorNormalizedChainComplexCoefficientMap_f_single.{a, b, w, p}
    g T 0 v x
  have hleft := congrArg
    (fun z : KB.X 0 ↦
      tensorNormalizedHomologyZeroToCoefficient.{b, w, max a p} B T hT
        (KB.homologyπ 0 ((ChainComplex.cycles₀Iso KB).inv z))) hf
  exact (hleft.trans
    (tensorNormalizedHomologyZeroToCoefficient_class.{b, w, max a p}
      B T hT v (g x))).trans
    (congrArg
      (fun z : ULift.{max b w p} A ↦ (ULift.up (g z.down) : ULift.{max a w p} B))
      (tensorNormalizedHomologyZeroToCoefficient_class.{a, w, max b p}
        A T hT v x)).symm

/-- A morphism between terminal simplicial sets preserves the degree-zero
coefficient comparison. -/
theorem tensorNormalizedHomologyZeroToCoefficient_naturality
    (A : Type a) [AddCommGroup A] (S T : SSet.{w})
    (hS : IsTerminal S) (hT : IsTerminal T) (f : S ⟶ T) :
    HomologicalComplex.homologyMap (tensorNormalizedChainComplexMap.{a, w, p} A f) 0 ≫
        tensorNormalizedHomologyZeroToCoefficient.{a, w, p} A T hT =
      tensorNormalizedHomologyZeroToCoefficient.{a, w, p} A S hS := by
  let K := tensorNormalizedChainComplex.{a, w, p} A S
  let L := tensorNormalizedChainComplex.{a, w, p} A T
  let F : K ⟶ L := tensorNormalizedChainComplexMap.{a, w, p} A f
  -- In degree zero, the cycles map is the original chain-map component.
  have hcycles :
      (ChainComplex.cycles₀Iso K).inv ≫ HomologicalComplex.cyclesMap F 0 =
        F.f 0 ≫ (ChainComplex.cycles₀Iso L).inv := by
    apply (cancel_mono (L.iCycles 0)).mp
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.iCyclesIso_inv_hom_id_assoc,
      HomologicalComplex.iCyclesIso_inv_hom_id, Category.comp_id]
  -- The homology projection is epic, and tensor generators span degree zero.
  change HomologicalComplex.homologyMap F 0 ≫
      tensorNormalizedHomologyZeroToCoefficient.{a, w, p} A T hT =
    tensorNormalizedHomologyZeroToCoefficient.{a, w, p} A S hS
  apply (cancel_epi (K.homologyπ 0)).mp
  apply (cancel_epi (ChainComplex.cycles₀Iso K).inv).mp
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  rw [← Category.assoc (ChainComplex.cycles₀Iso K).inv
    (HomologicalComplex.cyclesMap F 0), hcycles]
  simp only [Category.assoc]
  apply tensorNormalizedChainComplex_hom_ext.{a, w, p} A S 0
  intro v x
  let vT : T.nonDegenerate 0 := ⟨f.app (op ⦋0⦌) v.val, by simp⟩
  have hf :
      F.f 0 (ULift.up (Finsupp.single v 1 ⊗ₜ[ℤ] x)) =
        ULift.up (Finsupp.single vT 1 ⊗ₜ[ℤ] x) := by
    dsimp only [F]
    rw [tensorNormalizedChainComplexMap_f]
    change tensorNormalizedChainComplexXMap.{a, w, p} A f 0
        (ULift.up (Finsupp.single v 1 ⊗ₜ[ℤ] x) :
          ULift.{max a w p} ((S.nonDegenerate 0 →₀ ℤ) ⊗[ℤ] A)) =
      (ULift.up (Finsupp.single vT 1 ⊗ₜ[ℤ] x) :
        ULift.{max a w p} ((T.nonDegenerate 0 →₀ ℤ) ⊗[ℤ] A))
    rw [tensorNormalizedChainComplexXMap_single,
      T.normalizedIntegralSimplex_of_mem_nonDegenerate
        (f.app (op ⦋0⦌) v.val) vT.property]
  change tensorNormalizedHomologyZeroToCoefficient.{a, w, p} A T hT
      (L.homologyπ 0 ((ChainComplex.cycles₀Iso L).inv
        (F.f 0 (ULift.up (Finsupp.single v 1 ⊗ₜ[ℤ] x))))) =
    tensorNormalizedHomologyZeroToCoefficient.{a, w, p} A S hS
      (K.homologyπ 0 ((ChainComplex.cycles₀Iso K).inv
        (ULift.up (Finsupp.single v 1 ⊗ₜ[ℤ] x))))
  rw [hf, tensorNormalizedHomologyZeroToCoefficient_class.{a, w, p} A T hT vT x,
    tensorNormalizedHomologyZeroToCoefficient_class.{a, w, p} A S hS v x]

/-- The homology of normalized integral tensor chains vanishes in every degree
at least a dimension bound for the simplicial set. -/
theorem isZero_tensorNormalizedHomology_of_hasDimensionLT
    (A : Type a) [AddCommGroup A] (S : SSet.{w}) (n d : ℕ) [S.HasDimensionLT d]
    (h : d ≤ n) :
    IsZero ((tensorNormalizedChainComplex.{a, w, p} A S).homology n) := by
  have hN : IsZero
      ((S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).X n) :=
    S.isZero_normalizedChainComplex_X_of_hasDimensionLT
      (ModuleCat.of ℤ (ULift.{max w p} A)) n d h
  have hK : IsZero ((tensorNormalizedChainComplex.{a, w, p} A S).X n) :=
    hN.of_iso (HomologicalComplex.Hom.isoApp (tensorNormalizedChainIso.{a, w, p} A S) n)
  have hExact : (tensorNormalizedChainComplex.{a, w, p} A S).ExactAt n :=
    HomologicalComplex.ExactAt.of_isZero hK
  exact hExact.isZero_homology

/-- The positive-degree homology of the original normalized integral tensor
complex of a terminal simplicial set is zero. This is the nonnegatively indexed
positive part of the ordinary point dimension statement in May, *A Concise Course
in Algebraic Topology*, Chapter 13, §1, in the normalized simplicial setting of
Chapter 16, §4. -/
theorem isZero_tensorNormalizedHomology_succ
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T) (n : ℕ) :
    IsZero ((tensorNormalizedChainComplex.{a, w, p} A T).homology (n + 1)) := by
  let : T.HasDimensionLT 1 :=
    (hasDimensionLT_iff_of_iso
      (hT.uniqueUpToIso stdSimplex.isTerminalObj₀.{w}) 1).2
        (inferInstance : (Δ[0] : SSet.{w}).HasDimensionLT 1)
  exact isZero_tensorNormalizedHomology_of_hasDimensionLT.{a, w, p} A T (n + 1) 1
    (Nat.succ_le_succ (Nat.zero_le n))

end SSet
