/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicPowerLimit
import Mathlib.Data.ZMod.Basic

/-!
# Prime-supported residue diagrams

Positive integers supported on a set of primes index the finite cyclic residue
groups. An arrow from `n` to `d` reduces modulo `d`, where `d ∣ n`. Exact
index at every supported power level identifies this diagram with the
power-quotient diagram after choosing one topological generator. For a
torsion-free procyclic group, its infinite-exponent support also reconstructs
the group from these residues.

Reduction of residues commutes with the power-quotient transition under the
equivalences determined by the same generator. This identifies the two
diagrams naturally and transports the supported power-quotient limit
equivalence to the residue limit.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §7, before Proposition
  (1.7.7) (torsion-free reconstruction by supported residue limits); the arbitrary diagram
  comparison is built here.
- Mathlib, `Mathlib.Data.ZMod.Basic` and finite-quotient limits used by
  `ProcyclicPowerLimit` (residues and inverse-limit cones).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ProfiniteGrp

/-- Reduction of finite cyclic residues, transported to the universe of a
profinite-group diagram. -/
def residueReduction {d n : ℕ} (hdn : d ∣ n) :
    ULift.{u} (Multiplicative (ZMod n)) →*
      ULift.{u} (Multiplicative (ZMod d)) :=
  MulEquiv.ulift.symm.toMonoidHom.comp
    ((ZMod.castHom hdn (ZMod d)).toAddMonoidHom.toMultiplicative.comp
      MulEquiv.ulift.toMonoidHom)

/-- Reduction acts on a residue by the usual cast from `ZMod n` to `ZMod d`. -/
@[simp] theorem residueReduction_apply {d n : ℕ} (hdn : d ∣ n) (a : ZMod n) :
    residueReduction.{u} hdn (ULift.up (Multiplicative.ofAdd a)) =
      ULift.up (Multiplicative.ofAdd (ZMod.castHom hdn (ZMod d) a)) := rfl

/-- Reducing at the same positive or zero modulus is the identity. -/
@[simp] theorem residueReduction_id (n : ℕ) :
    residueReduction.{u} (dvd_refl n) = MonoidHom.id _ := by
  apply MonoidHom.ext
  rintro ⟨a⟩
  change ULift.up (Multiplicative.ofAdd
    (ZMod.castHom (dvd_refl n) (ZMod n) a.toAdd)) = ULift.up a
  simp [ZMod.castHom_self]

/-- Reductions compose along a divisibility chain. -/
@[simp] theorem residueReduction_comp {e d n : ℕ} (hed : e ∣ d) (hdn : d ∣ n) :
    (residueReduction.{u} hed).comp (residueReduction hdn) =
      residueReduction (dvd_trans hed hdn) := by
  apply MonoidHom.ext
  rintro ⟨a⟩
  change ULift.up (Multiplicative.ofAdd
    (ZMod.castHom hed (ZMod e) (ZMod.castHom hdn (ZMod d) a.toAdd))) =
    ULift.up (Multiplicative.ofAdd
      (ZMod.castHom (dvd_trans hed hdn) (ZMod e) a.toAdd))
  simp only [← RingHom.comp_apply, ZMod.castHom_comp]

/-- The finite-group diagram of supported cyclic residues. -/
def residueFiniteFunctor (S : Set Nat.Primes) : Nat.PowerIndex S ⥤ FiniteGrp.{u} where
  obj n := letI : NeZero n.val := ⟨n.pos.ne'⟩
    FiniteGrp.of (ULift.{u} (Multiplicative (ZMod n.val)))
  map {n d} f :=
    letI : NeZero n.val := ⟨n.pos.ne'⟩
    letI : NeZero d.val := ⟨d.pos.ne'⟩
    FiniteGrp.ofHom (residueReduction (Nat.PowerIndex.dvd_of_hom f))
  map_id n := by
    ext a
    exact congrFun (congrArg DFunLike.coe (residueReduction_id.{u} n.val)) a
  map_comp {n d e} f g := by
    ext a
    exact congrFun (congrArg DFunLike.coe
      (residueReduction_comp.{u} (Nat.PowerIndex.dvd_of_hom g)
        (Nat.PowerIndex.dvd_of_hom f)).symm) a

/-- A finite residue stage is the multiplicative group of residues modulo its
positive power index. -/
@[simp] theorem residueFiniteFunctor_obj (S : Set Nat.Primes) (n : Nat.PowerIndex S) :
    ((residueFiniteFunctor.{u} S).obj n : Type u) =
      ULift.{u} (Multiplicative (ZMod n.val)) := rfl

/-- Finite residue arrows reduce modulo the target power index. -/
@[simp] theorem residueFiniteFunctor_map_apply (S : Set Nat.Primes)
    {n d : Nat.PowerIndex S} (f : n ⟶ d) (a : ZMod n.val) :
    (residueFiniteFunctor.{u} S).map f (ULift.up (Multiplicative.ofAdd a)) =
      ULift.up (Multiplicative.ofAdd
        (ZMod.castHom (Nat.PowerIndex.dvd_of_hom f) (ZMod d.val) a)) :=
  residueReduction_apply.{u} _ _

/-- The profinite diagram of supported cyclic residues, with discrete stages. -/
def residueDiagram (S : Set Nat.Primes) : Nat.PowerIndex S ⥤ ProfiniteGrp.{u} :=
  residueFiniteFunctor.{u} S ⋙ (forget₂ FiniteGrp ProfiniteGrp)

/-- A residue stage is the discrete multiplicative group of residues modulo
the underlying positive power index. -/
@[simp] theorem residueDiagram_obj (S : Set Nat.Primes) (n : Nat.PowerIndex S) :
    ((residueDiagram.{u} S).obj n : Type u) =
      ULift.{u} (Multiplicative (ZMod n.val)) := residueFiniteFunctor_obj S n

/-- Diagram arrows act by reduction of residues. -/
@[simp] theorem residueDiagram_map_apply (S : Set Nat.Primes)
    {n d : Nat.PowerIndex S} (f : n ⟶ d) (a : ZMod n.val) :
    (residueDiagram.{u} S).map f (ULift.up (Multiplicative.ofAdd a)) =
      ULift.up (Multiplicative.ofAdd
        (ZMod.castHom (Nat.PowerIndex.dvd_of_hom f) (ZMod d.val) a)) :=
  residueFiniteFunctor_map_apply.{u} S f a

/-- Identity arrows leave every residue unchanged. -/
@[simp] theorem residueDiagram_map_id_apply (S : Set Nat.Primes)
    (n : Nat.PowerIndex S) (a : ZMod n.val) :
    (residueDiagram.{u} S).map (𝟙 n) (ULift.up (Multiplicative.ofAdd a)) =
      ULift.up (Multiplicative.ofAdd a) := by
  rw [(residueDiagram.{u} S).map_id]
  rfl

/-- Consecutive diagram arrows reduce to the same residue as their composite. -/
theorem residueDiagram_map_comp_apply (S : Set Nat.Primes)
    {n d e : Nat.PowerIndex S} (f : n ⟶ d) (g : d ⟶ e) (a : ZMod n.val) :
    (residueDiagram.{u} S).map g
        ((residueDiagram S).map f (ULift.up (Multiplicative.ofAdd a))) =
      (residueDiagram S).map (f ≫ g) (ULift.up (Multiplicative.ofAdd a)) := by
  exact congrArg (fun h => h (ULift.up (Multiplicative.ofAdd a)))
    ((residueDiagram.{u} S).map_comp f g).symm

/-- The chosen generator identifies residues at one exact-index power level
with the corresponding power quotient. -/
noncomputable def residuePowerQuotientComponent (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g)
    {S : Set Nat.Primes} (n : Nat.PowerIndex S)
    (hindex : (powerImage G hG n.val : Subgroup G).index = n.val) :
    (residueDiagram.{u} S).obj n ≅ (powerQuotientDiagram G hG S).obj n := by
  letI : DiscreteTopology ((residueDiagram.{u} S).obj n) := ⟨rfl⟩
  letI : DiscreteTopology ((powerQuotientDiagram G hG S).obj n) := ⟨rfl⟩
  let e : (residueDiagram.{u} S).obj n ≃ₜ*
      (powerQuotientDiagram G hG S).obj n :=
    ContinuousMulEquiv.mk
      ((MulEquiv.ulift :
        ULift.{u} (Multiplicative (ZMod n.val)) ≃* Multiplicative (ZMod n.val)).trans
        (powerImage_zmodContinuousMulEquiv G hG g hg n.val n.pos hindex).toMulEquiv)
      continuous_of_discreteTopology continuous_of_discreteTopology
  exact ContinuousMulEquiv.toProfiniteGrpIso e

/-- A component applies the chosen-generator cyclic quotient equivalence
after forgetting the universe lift on a residue. -/
@[simp] theorem residuePowerQuotientComponent_hom_apply (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g)
    {S : Set Nat.Primes} (n : Nat.PowerIndex S)
    (hindex : (powerImage G hG n.val : Subgroup G).index = n.val)
    (a : ZMod n.val) :
    (residuePowerQuotientComponent G hG g hg n hindex).hom
        (ULift.up (Multiplicative.ofAdd a)) =
      powerImage_zmodContinuousMulEquiv G hG g hg n.val n.pos hindex
        (Multiplicative.ofAdd a) := rfl

/-- The inverse component reads a quotient class as a residue in the
corresponding lifted cyclic group. -/
@[simp] theorem residuePowerQuotientComponent_inv_apply (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g)
    {S : Set Nat.Primes} (n : Nat.PowerIndex S)
    (hindex : (powerImage G hG n.val : Subgroup G).index = n.val)
    (q : G ⧸ (powerImage G hG n.val : Subgroup G)) :
    (residuePowerQuotientComponent G hG g hg n hindex).inv q =
      ULift.up ((powerImage_zmodContinuousMulEquiv G hG g hg n.val n.pos hindex).symm q) :=
  rfl

/-- At an exact-index level the component sends residue one to the chosen
generator's quotient class. -/
@[simp] theorem residuePowerQuotientComponent_hom_one (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g)
    {S : Set Nat.Primes} (n : Nat.PowerIndex S)
    (hindex : (powerImage G hG n.val : Subgroup G).index = n.val) :
    (residuePowerQuotientComponent G hG g hg n hindex).hom
        (ULift.up (Multiplicative.ofAdd (1 : ZMod n.val))) =
      QuotientGroup.mk' (powerImage G hG n.val : Subgroup G) g := by
  rw [residuePowerQuotientComponent_hom_apply,
    powerImage_zmodContinuousMulEquiv_apply_one]

/-- Generator-normalized natural comparison at all exact-index supported
levels; it does not require torsion-freeness. -/
noncomputable def residuePowerQuotientNatIso (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g)
    (S : Set Nat.Primes)
    (hindex : ∀ n : Nat.PowerIndex S,
      (powerImage G hG n.val : Subgroup G).index = n.val) :
    residueDiagram.{u} S ≅ powerQuotientDiagram G hG S :=
  NatIso.ofComponents
    (fun n ↦ residuePowerQuotientComponent G hG g hg n (hindex n))
    (by
      intro n d f
      ext ⟨a⟩
      change (residuePowerQuotientComponent G hG g hg d (hindex d)).hom
          ((residueDiagram S).map f (ULift.up (Multiplicative.ofAdd a.toAdd))) =
        (powerQuotientDiagram G hG S).map f
          ((residuePowerQuotientComponent G hG g hg n (hindex n)).hom
            (ULift.up (Multiplicative.ofAdd a.toAdd)))
      simp only [residueDiagram_map_apply,
        residuePowerQuotientComponent_hom_apply, powerQuotientDiagram_map_apply]
      change powerImage_zmodContinuousMulEquiv G hG g hg d.val d.pos (hindex d)
          (Multiplicative.ofAdd
            (ZMod.castHom (Nat.PowerIndex.dvd_of_hom f) (ZMod d.val) a.toAdd)) =
        powerImage_quotientMap G hG (Nat.PowerIndex.dvd_of_hom f)
          (powerImage_zmodContinuousMulEquiv G hG g hg n.val n.pos (hindex n)
            (Multiplicative.ofAdd a.toAdd))
      exact (powerImage_quotientMap_zmod G hG g hg
        (Nat.PowerIndex.dvd_of_hom f) n.pos (hindex n) a.toAdd).symm)

/-- The natural comparison's component is the chosen-generator equivalence
on residues at every exact-index level. -/
@[simp] theorem residuePowerQuotientNatIso_hom_apply (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g)
    (S : Set Nat.Primes)
    (hindex : ∀ n : Nat.PowerIndex S,
      (powerImage G hG n.val : Subgroup G).index = n.val)
    (n : Nat.PowerIndex S) (a : ZMod n.val) :
    (residuePowerQuotientNatIso G hG g hg S hindex).hom.app n
        (ULift.up (Multiplicative.ofAdd a)) =
      powerImage_zmodContinuousMulEquiv G hG g hg n.val n.pos (hindex n)
        (Multiplicative.ofAdd a) := by
  exact residuePowerQuotientComponent_hom_apply G hG g hg n (hindex n) a

/-- Naturality says that the same chosen generator commutes with reduction
and passage to a coarser power quotient. -/
theorem residuePowerQuotientNatIso_naturality_apply (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g)
    (S : Set Nat.Primes)
    (hindex : ∀ n : Nat.PowerIndex S,
      (powerImage G hG n.val : Subgroup G).index = n.val)
    {n d : Nat.PowerIndex S} (f : n ⟶ d) (a : ZMod n.val) :
    (powerQuotientDiagram G hG S).map f
        ((residuePowerQuotientNatIso G hG g hg S hindex).hom.app n
          (ULift.up (Multiplicative.ofAdd a))) =
      (residuePowerQuotientNatIso G hG g hg S hindex).hom.app d
        ((residueDiagram.{u} S).map f (ULift.up (Multiplicative.ofAdd a))) := by
  exact congrArg (fun h => h (ULift.up (Multiplicative.ofAdd a)))
    ((residuePowerQuotientNatIso G hG g hg S hindex).hom.naturality f).symm

/-- Every power level supported on infinite-exponent primes has exact index,
even when the procyclic group has torsion elsewhere. -/
theorem powerImage_index_eq_of_infiniteSupport (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (S : Set Nat.Primes)
    (hS : S ⊆ {p | hG.exponents p = ⊤}) (n : Nat.PowerIndex S) :
    (powerImage G hG n.val : Subgroup G).index = n.val := by
  apply (powerImage_index_eq_iff_exponents G hG n.val n.pos).mpr
  intro p
  by_cases hp : n.val.factorization p.1 = 0
  · simp [hp]
  · have hmem := (Nat.mem_primeSupportedIndices_iff_factorization.mp n.property).2 p hp
    rw [hS hmem]
    exact le_top

/-- The comparison for a subset of the infinite-exponent support uses only
procyclicity and the one supplied topological generator. -/
noncomputable def residuePowerQuotientNatIsoOfInfiniteSupport
    (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (g : G) (hg : IsTopologicalGenerator G g)
    (S : Set Nat.Primes) (hS : S ⊆ {p | hG.exponents p = ⊤}) :
    residueDiagram.{u} S ≅ powerQuotientDiagram G hG S :=
  residuePowerQuotientNatIso G hG g hg S
    (powerImage_index_eq_of_infiniteSupport G hG S hS)

/-- Transport between the explicit power-quotient and residue limits, induced
by the generator-normalized comparison at exact-index levels. -/
noncomputable def powerQuotientLimitIsoResidue (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g)
    (S : Set Nat.Primes)
    (hindex : ∀ n : Nat.PowerIndex S,
      (powerImage G hG n.val : Subgroup G).index = n.val) :
    ProfiniteGrp.limit (powerQuotientDiagram G hG S) ≅
      ProfiniteGrp.limit (residueDiagram.{u} S) :=
  IsLimit.conePointsIsoOfNatIso
    (ProfiniteGrp.limitConeIsLimit (powerQuotientDiagram G hG S))
    (ProfiniteGrp.limitConeIsLimit (residueDiagram.{u} S))
    (residuePowerQuotientNatIso G hG g hg S hindex).symm

/-- Limit transport reads each residue coordinate using the inverse
chosen-generator component at that same level. -/
@[simp] theorem powerQuotientLimitIsoResidue_hom_apply
    (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (g : G) (hg : IsTopologicalGenerator G g) (S : Set Nat.Primes)
    (hindex : ∀ n : Nat.PowerIndex S,
      (powerImage G hG n.val : Subgroup G).index = n.val)
    (n : Nat.PowerIndex S) (x : ProfiniteGrp.limit (powerQuotientDiagram G hG S)) :
    ((powerQuotientLimitIsoResidue G hG g hg S hindex).hom x).val n =
      (residuePowerQuotientNatIso G hG g hg S hindex).inv.app n (x.val n) := by
  have h := congrArg
    (fun f : ProfiniteGrp.limit (powerQuotientDiagram G hG S) ⟶
        (residueDiagram.{u} S).obj n => f x)
    (IsLimit.conePointsIsoOfNatIso_hom_comp
      (ProfiniteGrp.limitConeIsLimit (powerQuotientDiagram G hG S))
      (ProfiniteGrp.limitConeIsLimit (residueDiagram.{u} S))
      (residuePowerQuotientNatIso G hG g hg S hindex).symm n)
  exact h

/-- The torsion-free supported reconstruction, transported from power
quotients to the residue diagram by the chosen-generator comparison.

The torsion-free supported-residue reconstruction comes from Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, Ch. I §7, before Proposition (1.7.7); a chosen generator
normalizes the coordinates. -/
noncomputable def continuousMulEquivSupportedResidueLimit (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (hfree : IsMulTorsionFree G)
    (g : G) (hg : IsTopologicalGenerator G g) :
    G ≃ₜ* ProfiniteGrp.limit
      (residueDiagram.{u} {p | hG.exponents p = ⊤}) := by
  let iso := powerQuotientLimitIsoResidue G hG g hg
    {p | hG.exponents p = ⊤}
    (powerImage_index_eq_of_infiniteSupport G hG _ (Set.Subset.rfl))
  exact (continuousMulEquivSupportedPowerQuotientLimit G hG hfree).trans
    { CompHausLike.homeoOfIso ((forget₂ ProfiniteGrp Profinite).mapIso iso) with
      map_mul' := map_mul iso.hom.hom }

/-- Each residue coordinate is the inverse chosen-generator quotient
coordinate at the same supported positive level. -/
@[simp] theorem continuousMulEquivSupportedResidueLimit_apply
    (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) (hfree : IsMulTorsionFree G)
    (g : G) (hg : IsTopologicalGenerator G g)
    (n : Nat.PowerIndex {p | hG.exponents p = ⊤}) (x : G) :
    (continuousMulEquivSupportedResidueLimit G hG hfree g hg x).val n =
      (residuePowerQuotientNatIsoOfInfiniteSupport G hG g hg
        {p | hG.exponents p = ⊤} (Set.Subset.rfl)).inv.app n
        (QuotientGroup.mk' (powerImage G hG n.val : Subgroup G) x) := by
  change ((powerQuotientLimitIsoResidue G hG g hg _
    (powerImage_index_eq_of_infiniteSupport G hG _ (Set.Subset.rfl))).hom
      (continuousMulEquivSupportedPowerQuotientLimit G hG hfree x)).val n = _
  rw [powerQuotientLimitIsoResidue_hom_apply,
    continuousMulEquivSupportedPowerQuotientLimit_apply]
  rfl

/-- Composing a residue coordinate with the comparison recovers the canonical
power-quotient coordinate. -/
@[simp] theorem continuousMulEquivSupportedResidueLimit_quotient_apply
    (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) (hfree : IsMulTorsionFree G)
    (g : G) (hg : IsTopologicalGenerator G g)
    (n : Nat.PowerIndex {p | hG.exponents p = ⊤}) (x : G) :
    (residuePowerQuotientNatIsoOfInfiniteSupport G hG g hg
      {p | hG.exponents p = ⊤} (Set.Subset.rfl)).hom.app n
      ((continuousMulEquivSupportedResidueLimit G hG hfree g hg x).val n) =
        QuotientGroup.mk' (powerImage G hG n.val : Subgroup G) x := by
  rw [continuousMulEquivSupportedResidueLimit_apply]
  let comparison := residuePowerQuotientNatIsoOfInfiniteSupport G hG g hg
    {p | hG.exponents p = ⊤} (Set.Subset.rfl)
  exact (comparison.app n).inv_hom_id_apply _

/-- The chosen generator has residue one in every supported coordinate. -/
@[simp] theorem continuousMulEquivSupportedResidueLimit_generator
    (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) (hfree : IsMulTorsionFree G)
    (g : G) (hg : IsTopologicalGenerator G g)
    (n : Nat.PowerIndex {p | hG.exponents p = ⊤}) :
    (continuousMulEquivSupportedResidueLimit G hG hfree g hg g).val n =
      ULift.up (Multiplicative.ofAdd (1 : ZMod n.val)) := by
  rw [continuousMulEquivSupportedResidueLimit_apply]
  change ULift.up
    ((powerImage_zmodContinuousMulEquiv G hG g hg n.val n.pos
      (powerImage_index_eq_of_infiniteSupport G hG _ (Set.Subset.rfl) n)).symm
        (QuotientGroup.mk' (powerImage G hG n.val : Subgroup G) g)) = _
  exact congrArg ULift.up
    (powerImage_zmodContinuousMulEquiv_symm_apply_generator G hG g hg n.val n.pos
      (powerImage_index_eq_of_infiniteSupport G hG _ (Set.Subset.rfl) n))

end ProfiniteGrp
