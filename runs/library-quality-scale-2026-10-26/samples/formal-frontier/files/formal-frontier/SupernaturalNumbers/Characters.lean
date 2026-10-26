/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SupernaturalNumbers.Order
public import GroupTheory.Topology.RationalCircle
public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Topology.Algebra.PontryaginDual

/-!
# Character groups of abelian torsion groups

This file identifies rational-circle characters of an abelian torsion group
with its circle-valued Pontryagin dual when the group is discrete.  It proves
that this dual is profinite and compares its supernatural order with the
finite-subgroup definition of torsion order.

The rational-circle inclusions and finite-order preimages are supplied by
`GroupTheory.Topology.RationalCircle`; the former `Supernatural` names remain
as deprecated compatibility aliases.
-/

@[expose] public section

open scoped Pointwise

namespace Supernatural

noncomputable section

/-- The canonical inclusion from the rational circle into the real additive circle. -/
@[deprecated (since := "2026-10-07")]
alias rationalAddCircleToReal := AddCircle.rationalToReal

/-- The canonical inclusion evaluated on a rational representative. -/
@[deprecated (since := "2026-10-07")]
alias rationalAddCircleToReal_mk := AddCircle.rationalToReal_mk

/-- The canonical inclusion into the real additive circle is injective. -/
@[deprecated (since := "2026-10-07")]
alias rationalAddCircleToReal_injective := AddCircle.rationalToReal_injective

/-- The canonical inclusion from the rational circle into the unit circle. -/
@[deprecated (since := "2026-10-07")]
alias rationalCircleToCircle := AddCircle.rationalToCircle

/-- The canonical inclusion into the unit circle is injective. -/
@[deprecated (since := "2026-10-07")]
alias rationalCircleToCircle_injective := AddCircle.rationalToCircle_injective

/-- Every finite-order point of the real additive circle has a rational preimage. -/
@[deprecated (since := "2026-10-07")]
alias exists_rational_preimage_of_isOfFinAddOrder :=
  AddCircle.exists_rational_preimage_of_isOfFinAddOrder

/-- Every finite-order point of the unit circle has a rational preimage. -/
@[deprecated (since := "2026-10-07")]
alias exists_rationalCircle_preimage_of_isOfFinOrder :=
  Circle.exists_rational_preimage_of_isOfFinOrder

variable (A : Type*) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]

/-- The roots of a positive power in the unit circle form a finite set. -/
theorem circle_roots_finite (n : ℕ) (hn : 0 < n) :
    {z : Circle | z ^ n = 1}.Finite := by
  let e := AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)
  apply Set.Finite.of_preimage (f := e) (s := {z : Circle | z ^ n = 1})
  · have heq : e ⁻¹' {z : Circle | z ^ n = 1} =
        {u : AddCircle (1 : ℝ) | n • u = 0} := by
      ext u
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, e, AddCircle.homeomorphCircle_apply]
      rw [← AddCircle.toCircle_nsmul]
      rw [← AddCircle.toCircle_zero (T := (1 : ℝ))]
      exact (AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)).eq_iff
    rw [heq]
    exact AddCircle.finite_torsion (1 : ℝ) hn
  · exact e.surjective

omit [DiscreteTopology A] in
/-- Evaluating a circle-valued character at an element and raising to its
additive order gives one. -/
theorem character_pow_addOrderOf
    (χ : PontryaginDual (Multiplicative A)) (a : Multiplicative A) :
    χ a ^ addOrderOf a.toAdd = 1 := by
  calc
    χ a ^ addOrderOf a.toAdd = χ (a ^ addOrderOf a.toAdd) := (map_pow χ a _).symm
    _ = χ 1 := by
      congr 1
      apply Multiplicative.toAdd.injective
      exact addOrderOf_nsmul_eq_zero a.toAdd
    _ = 1 := map_one χ

omit [DiscreteTopology A] in
/-- The Pontryagin dual of a topological abelian torsion group is totally
disconnected. -/
theorem pontryaginDual_totallyDisconnected (hA : IsAddTorsion A) :
    TotallyDisconnectedSpace (PontryaginDual (Multiplicative A)) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  intro χ
  apply Set.Subset.antisymm
  · intro ψ hψ
    have hψχ : ψ = χ := PontryaginDual.ext fun a ↦ by
      let roots : Set Circle := {z | z ^ addOrderOf a.toAdd = 1}
      let ev : PontryaginDual (Multiplicative A) → roots := fun φ ↦
        ⟨φ a, character_pow_addOrderOf A φ a⟩
      let _ : Fintype roots :=
        (circle_roots_finite (addOrderOf a.toAdd) (hA a.toAdd).addOrderOf_pos).fintype
      have hevval : Continuous (fun φ : PontryaginDual (Multiplicative A) ↦ φ a) := by
        change Continuous (fun φ : (Multiplicative A →ₜ* Circle) ↦ φ a)
        exact continuous_eval_const a
      have hev : Continuous ev :=
        hevval.subtype_mk _
      have himage := hev.image_connectedComponent_eq_singleton χ
      have hevψ : ev ψ ∈ ev '' connectedComponent χ := ⟨ψ, hψ, rfl⟩
      rw [himage] at hevψ
      exact congrArg Subtype.val (Set.mem_singleton_iff.mp hevψ)
    exact hψχ ▸ Set.mem_singleton χ
  · exact Set.singleton_subset_iff.mpr mem_connectedComponent

/-- The Pontryagin dual of a discrete abelian torsion group as a profinite group. -/
def profinitePontryaginDual (hA : IsAddTorsion A) : ProfiniteGrp := by
  let _ : TotallyDisconnectedSpace (PontryaginDual (Multiplicative A)) :=
    pontryaginDual_totallyDisconnected A hA
  exact ProfiniteGrp.of (PontryaginDual (Multiplicative A))

/-- Postcompose a rational character with the standard inclusion into the circle. -/
def characterToPontryagin (c : CharacterModule A) :
    PontryaginDual (Multiplicative A) where
  toFun a := Additive.toMul (AddCircle.rationalToCircle (c a.toAdd))
  map_one' := by simp
  map_mul' a b := by
    change Additive.toMul (AddCircle.rationalToCircle (c (a.toAdd + b.toAdd))) =
      Additive.toMul (AddCircle.rationalToCircle (c a.toAdd)) *
        Additive.toMul (AddCircle.rationalToCircle (c b.toAdd))
    rw [map_add, map_add]
    rfl
  continuous_toFun := continuous_of_discreteTopology

/-- Postcomposition with the rational-circle embedding as an additive homomorphism. -/
def characterToPontryaginHom :
    CharacterModule A →+ Additive (PontryaginDual (Multiplicative A)) where
  toFun c := Additive.ofMul (characterToPontryagin A c)
  map_zero' := by
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro a
    change Additive.toMul (AddCircle.rationalToCircle (0 : AddCircle (1 : ℚ))) = 1
    simp
  map_add' c d := by
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro a
    change Additive.toMul (AddCircle.rationalToCircle (c a.toAdd + d a.toAdd)) =
      Additive.toMul (AddCircle.rationalToCircle (c a.toAdd)) *
        Additive.toMul (AddCircle.rationalToCircle (d a.toAdd))
    rw [map_add]
    rfl

/-- Postcomposition identifies rational and circle-valued characters of a
discrete abelian torsion group. -/
theorem characterToPontryaginHom_bijective (hA : IsAddTorsion A) :
    Function.Bijective (characterToPontryaginHom A) := by
  constructor
  · intro c d hcd
    apply CharacterModule.ext
    intro a
    apply AddCircle.rationalToCircle_injective
    apply Additive.toMul.injective
    have h := congrArg Additive.toMul hcd
    exact congrArg (fun χ : PontryaginDual (Multiplicative A) ↦ χ (Multiplicative.ofAdd a)) h
  · intro χ
    have hfin (a : A) : IsOfFinOrder (Additive.toMul χ (Multiplicative.ofAdd a)) :=
      isOfFinOrder_iff_pow_eq_one.mpr
        ⟨addOrderOf a, (hA a).addOrderOf_pos,
          character_pow_addOrderOf A (Additive.toMul χ) (Multiplicative.ofAdd a)⟩
    choose q hq using fun a ↦ Circle.exists_rational_preimage_of_isOfFinOrder (hfin a)
    let c : CharacterModule A :=
      { toFun := q
        map_zero' := by
          apply AddCircle.rationalToCircle_injective
          apply Additive.toMul.injective
          rw [hq]
          simp
        map_add' := by
          intro a b
          apply AddCircle.rationalToCircle_injective
          apply Additive.toMul.injective
          calc
            Additive.toMul (AddCircle.rationalToCircle (q (a + b))) =
                Additive.toMul χ (Multiplicative.ofAdd (a + b)) := hq (a + b)
            _ = Additive.toMul χ (Multiplicative.ofAdd a * Multiplicative.ofAdd b) := rfl
            _ = Additive.toMul χ (Multiplicative.ofAdd a) *
                Additive.toMul χ (Multiplicative.ofAdd b) := map_mul _ _ _
            _ = Additive.toMul (AddCircle.rationalToCircle (q a)) *
                Additive.toMul (AddCircle.rationalToCircle (q b)) := by rw [hq, hq]
            _ = Additive.toMul (AddCircle.rationalToCircle (q a + q b)) := by
              rw [map_add]
              rfl }
    refine ⟨c, ?_⟩
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro a
    exact hq a.toAdd

/-- Algebraic characters in `ℚ/ℤ` are exactly circle-valued continuous
characters of the underlying discrete torsion group. -/
def characterEquivPontryagin (hA : IsAddTorsion A) :
    CharacterModule A ≃+ Additive (PontryaginDual (Multiplicative A)) :=
  AddEquiv.ofBijective (characterToPontryaginHom A)
    (characterToPontryaginHom_bijective A hA)

/-- Forget continuity and translate multiplicative/additive type tags for a
discrete source group. -/
def pontryaginEquivAddChar :
    PontryaginDual (Multiplicative A) ≃ AddChar A Circle where
  toFun χ :=
    { toFun := fun a ↦ χ (Multiplicative.ofAdd a)
      map_zero_eq_one' := map_one χ
      map_add_eq_mul' := fun a b ↦ map_mul χ (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) }
  invFun χ :=
    { toFun := fun a ↦ χ a.toAdd
      map_one' := χ.map_zero_eq_one
      map_mul' := χ.map_add_eq_mul
      continuous_toFun := continuous_of_discreteTopology }
  left_inv _χ := PontryaginDual.ext fun _ ↦ rfl
  right_inv _χ := AddChar.ext _ _ fun _ ↦ rfl

/-- The Pontryagin dual of a finite abelian group has the same cardinality. -/
theorem natCard_pontryaginDual_eq [Finite A] :
    Nat.card (PontryaginDual (Multiplicative A)) = Nat.card A := by
  rw [Nat.card_congr (pontryaginEquivAddChar A)]
  rw [Nat.card_congr AddChar.circleEquivComplex.toEquiv]
  cases nonempty_fintype A
  simpa only [Nat.card_eq_fintype_card] using AddChar.card_eq (α := A)

/-- Inclusion of an additive subgroup, with multiplicative type tags. -/
def multiplicativeSubgroupInclusion (B : AddSubgroup A) :
    Multiplicative B →ₜ* Multiplicative A where
  toFun b := Multiplicative.ofAdd b.toAdd.1
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_of_discreteTopology

/-- Restriction of circle-valued characters to an additive subgroup. -/
def pontryaginRestriction (B : AddSubgroup A) :
    PontryaginDual (Multiplicative A) →ₜ* PontryaginDual (Multiplicative B) :=
  PontryaginDual.map (multiplicativeSubgroupInclusion A B)

/-- Every circle-valued character of a subgroup of an abelian torsion group
extends to the whole group. -/
theorem pontryaginRestriction_surjective (hA : IsAddTorsion A) (B : AddSubgroup A) :
    Function.Surjective (pontryaginRestriction A B) := by
  intro χ
  let hB : IsAddTorsion B := fun b ↦
    B.subtype_injective.isOfFinAddOrder_iff.mp (hA b.1)
  let cB : CharacterModule B :=
    (characterEquivPontryagin B hB).symm (Additive.ofMul χ)
  let f : B →ₗ[ℤ] A := B.subtype.toIntLinearMap
  obtain ⟨c, hc⟩ := CharacterModule.dual_surjective_of_injective f
    B.subtype_injective cB
  refine ⟨characterToPontryagin A c, ?_⟩
  apply PontryaginDual.ext
  intro b
  have hcb : c b.1 = cB b := by
    exact congrArg (fun d : CharacterModule B ↦ d b) hc
  have hcB : characterToPontryagin B cB = χ := by
    exact congrArg Additive.toMul
      ((characterEquivPontryagin B hB).apply_symm_apply (Additive.ofMul χ))
  change Additive.toMul (AddCircle.rationalToCircle (c b.1)) = χ b
  rw [hcb]
  exact congrArg (fun ψ : PontryaginDual (Multiplicative B) ↦ ψ b) hcB

/-- The open normal subgroup of characters vanishing on a finite subgroup. -/
def pontryaginRestrictionKernel (B : AddSubgroup A) [Finite B] :
    OpenNormalSubgroup (PontryaginDual (Multiplicative A)) where
  toOpenSubgroup :=
    { toSubgroup := (pontryaginRestriction A B).ker
      isOpen' := by
        change IsOpen ((pontryaginRestriction A B) ⁻¹' ({1} : Set _))
        exact (isOpen_discrete {1}).preimage (pontryaginRestriction A B).continuous }
  isNormal' := Subgroup.normal_of_isMulCommutative _

/-- The restriction kernel associated to a finite subgroup has index equal to
the cardinality of that subgroup. -/
theorem pontryaginRestrictionKernel_index (hA : IsAddTorsion A)
    (B : AddSubgroup A) [Finite B] :
    (pontryaginRestrictionKernel A B).toSubgroup.index = Nat.card B := by
  rw [show (pontryaginRestrictionKernel A B).toSubgroup =
    (pontryaginRestriction A B).ker from rfl]
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (pontryaginRestriction_surjective A hA B)]
  simpa using natCard_pontryaginDual_eq B

/-- The quotient by a finite-subgroup restriction kernel has the expected cardinality. -/
theorem natCard_quotient_pontryaginRestrictionKernel (hA : IsAddTorsion A)
    (B : AddSubgroup A) [Finite B] :
    Nat.card (PontryaginDual (Multiplicative A) ⧸
      (pontryaginRestrictionKernel A B).toSubgroup) = Nat.card B := by
  rw [← Subgroup.index_eq_card]
  exact pontryaginRestrictionKernel_index A hA B

/-- Kernels of restriction to finite subgroups are cofinal among open normal
subgroups of the Pontryagin dual. -/
theorem exists_pontryaginRestrictionKernel_le (hA : IsAddTorsion A)
    (U : OpenNormalSubgroup (PontryaginDual (Multiplicative A))) :
    ∃ (B : AddSubgroup A) (_ : Finite B), pontryaginRestrictionKernel A B ≤ U := by
  classical
  let f : PontryaginDual (Multiplicative A) → (Multiplicative A → Circle) := fun χ ↦ χ
  have hf : Topology.IsInducing f := by
    change Topology.IsInducing
      ((⇑) : (Multiplicative A →ₜ* Circle) → (Multiplicative A → Circle))
    exact ContinuousMonoidHom.isClosedEmbedding_coe.toIsEmbedding.toIsInducing
  obtain ⟨O, hO, hOU⟩ := hf.isOpen_iff.mp U.isOpen'
  have h1O : f 1 ∈ O := by
    rw [← Set.mem_preimage, hOU]
    exact U.one_mem
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hO (f 1) h1O
  let S : Finset A := I.image Multiplicative.toAdd
  let B : AddSubgroup A := AddSubgroup.closure (S : Set A)
  have hBtors : IsAddTorsion B := fun b ↦
    B.subtype_injective.isOfFinAddOrder_iff.mp (hA b.1)
  let _ : Finite B := AddCommGroup.finite_of_fg_isAddTorsion B hBtors
  refine ⟨B, inferInstance, ?_⟩
  intro χ hχ
  have hfχ : f χ ∈ O := by
    apply hsub
    intro a haI
    have haIfin : a ∈ I := haI
    have haS : a.toAdd ∈ S := by simp [S, haIfin]
    let b : B := ⟨a.toAdd, AddSubgroup.subset_closure haS⟩
    have hrest : (pontryaginRestriction A B χ) (Multiplicative.ofAdd b) = 1 := by
      have hk : pontryaginRestriction A B χ = 1 := hχ
      exact congrArg (fun ψ : PontryaginDual (Multiplicative B) ↦
        ψ (Multiplicative.ofAdd b)) hk
    have hχa : χ a = 1 := hrest
    change χ a ∈ u a
    rw [hχa]
    exact (hu a haI).2
  have hpre : χ ∈ f ⁻¹' O := hfχ
  rw [hOU] at hpre
  exact hpre

/-- The profinite character group of an abelian torsion group, formed after
equipping the source with its discrete topology. -/
def profiniteCharacter (A : Type*) [AddCommGroup A] (hA : IsAddTorsion A) : ProfiniteGrp := by
  let _ : TopologicalSpace A := ⊥
  let _ : DiscreteTopology A := discreteTopology_bot A
  exact profinitePontryaginDual A hA

/-- Rational-circle characters are the underlying additive group of the
topology-free profinite character group. -/
def characterEquivProfiniteCharacter
    (A : Type*) [AddCommGroup A] (hA : IsAddTorsion A) :
    CharacterModule A ≃+ Additive (profiniteCharacter A hA) := by
  letI : TopologicalSpace A := ⊥
  let _ : DiscreteTopology A := discreteTopology_bot A
  exact characterEquivPontryagin A hA

/-- For a chosen discrete topology, torsion order equals the supernatural order
of the Pontryagin dual. -/
theorem torsionOrder_eq_profiniteOrder_pontryagin (hA : IsAddTorsion A) :
    torsionOrder A hA = profiniteOrder (profinitePontryaginDual A hA) := by
  let _ : TotallyDisconnectedSpace (PontryaginDual (Multiplicative A)) :=
    pontryaginDual_totallyDisconnected A hA
  change torsionOrder A hA =
    ⨆ U : OpenNormalSubgroup (PontryaginDual (Multiplicative A)),
      ofFiniteCard (PontryaginDual (Multiplicative A) ⧸ U.toSubgroup)
  apply le_antisymm
  · refine iSup_le fun B ↦ ?_
    let _ : Finite B.1 := B.2
    let U := pontryaginRestrictionKernel A B.1
    calc
      @ofFiniteCard B.1 B.2 (inferInstanceAs (Nonempty B.1)) =
          ofFiniteCard (PontryaginDual (Multiplicative A) ⧸ U.toSubgroup) := by
            simp only [ofFiniteCard]
            apply congrArg ofPNat
            apply Subtype.ext
            exact (natCard_quotient_pontryaginRestrictionKernel A hA B.1).symm
      _ ≤ ⨆ V : OpenNormalSubgroup (PontryaginDual (Multiplicative A)),
          ofFiniteCard (PontryaginDual (Multiplicative A) ⧸ V.toSubgroup) :=
        le_iSup (fun V : OpenNormalSubgroup (PontryaginDual (Multiplicative A)) ↦
          ofFiniteCard (PontryaginDual (Multiplicative A) ⧸ V.toSubgroup)) U
  · refine iSup_le fun U ↦ ?_
    obtain ⟨B, hBfin, hBU⟩ := exists_pontryaginRestrictionKernel_le A hA U
    let _ : Finite B := hBfin
    calc
      ofFiniteCard (PontryaginDual (Multiplicative A) ⧸ U.toSubgroup) ≤
          ofFiniteCard B := by
        simp only [ofFiniteCard]
        apply ofPNat_le_ofPNat_iff.mpr
        apply PNat.dvd_iff.mpr
        change Nat.card (PontryaginDual (Multiplicative A) ⧸ U.toSubgroup) ∣ Nat.card B
        simpa only [Subgroup.index_eq_card,
          natCard_quotient_pontryaginRestrictionKernel A hA B] using
            Subgroup.index_dvd_of_le hBU
      _ ≤ torsionOrder A hA :=
        finiteAddSubgroupOrder_le_torsionOrder A hA ⟨B, inferInstance⟩

/-- The supernatural order of an abelian torsion group equals the supernatural
order of its profinite character group. -/
theorem torsionOrder_eq_profiniteOrder_character
    (A : Type*) [AddCommGroup A] (hA : IsAddTorsion A) :
    torsionOrder A hA = profiniteOrder (profiniteCharacter A hA) := by
  let _ : TopologicalSpace A := ⊥
  let _ : DiscreteTopology A := discreteTopology_bot A
  exact torsionOrder_eq_profiniteOrder_pontryagin A hA

end

end Supernatural
