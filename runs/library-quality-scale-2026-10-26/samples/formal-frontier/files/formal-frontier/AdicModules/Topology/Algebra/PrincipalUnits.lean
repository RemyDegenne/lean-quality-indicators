/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.Polynomial.Hensel
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.LinearAlgebra.SModEq.Pow
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Algebra.Module.Defs

import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Powers of principal units

For a Henselian pair `(R, I)`, the natural `n`-th power map on the kernel of
reduction `Rˣ → (R ⧸ I)ˣ` is bijective whenever `n` is a unit in `R ⧸ I`.
This uses the existing subgroup and its natural powers; no topology or
positivity assumption on `n` is required. The proof uses simple-root lifting
from `AdicModules.Polynomial.Hensel`, together with Mathlib's finite geometric
sums and reflection of units modulo ideals contained in the Jacobson radical.

Let `R` be an algebraically `I`-adically complete commutative ring, and
suppose that the prime `p` belongs to `I`. The kernel of reduction
`Rˣ → (R ⧸ I)ˣ` admits canonical powers by `ℤ_[p]`, without choosing a topology
on `R`. The construction `Ideal.padicPow` extends all integer powers, including
negative powers. Its additive interpretation is the explicitly supplied module
`Ideal.padicModule`. When the displayed topology on `R` is `I`-adic, powering
and scalar multiplication are jointly continuous. Neither finite residue rings,
odd residue characteristic nor absence of torsion is required.

This is the ring-level form of Fesenko–Vostokov, Chapter I, (6.1). For valuation
integers the algebraic comparison is Mathlib's
`ValuationSubring.principalUnitGroupEquiv`; identifying its topologies and
specializing the completeness hypotheses are separate questions. No basis
statement for the principal units is asserted here.

## Implementation notes

For `a : ℤ_[p]` and a principal unit `v`, the powers
`((v : Rˣ) : R) ^ a.appr n` are compatible modulo `I ^ n` by
`SModEq.pow_pow_add_one` and the compatibility of the p-adic approximations.
`IsPrecomplete.prec'` gives their algebraic adic limit, and
`IsHausdorff.eq_iff_smodEq` makes it unique. The limit is one modulo `I`;
`IsAdicComplete.le_jacobson_bot` recovers its unit status. Congruences modulo
every `I ^ n` characterize the powers and their algebraic laws, without any
displayed topology or separate assumption of kernel-uniform completeness.

Only the continuity, sequence-limit and continuous-uniqueness assertions use
a displayed `I`-adic topology. The topology on the kernel is the existing
subgroup topology on units. Ring compatibility follows from `IsAdic I`, and
`IsOpenUnits.of_isAdic` compares the units topology with the ring topology.
No uniform structure on `R` or uniform-embedding property of `Units.val` is
assumed.

The module is a value rather than a global instance: `hpI` is not inferable
from the scalar and vector types. Its evaluation lemma specifies the scalar
operation without installing an instance in a theorem statement.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*,
  second edition, Chapter I, (6.1), p. 17.
* Mathlib's p-adic approximations, algebraic adic completeness and units topology;
  its power congruences in `LinearAlgebra.SModEq.Pow`.
-/

@[expose] public section

open Filter
open scoped Topology

universe u v

/-- A jointly continuous extension of integer powers to `ℤ_[p]` satisfies the power laws.
Hausdorffness identifies continuous maps agreeing on the dense integer exponents. -/
private theorem padicPower_laws_of_continuous_of_intCast
    {G : Type v} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {p : ℕ} [Fact p.Prime] (Q : ℤ_[p] → G → G)
    (hQ : Continuous (fun t : ℤ_[p] × G => Q t.1 t.2))
    (hQint : ∀ (m : ℤ) (v : G), Q (m : ℤ_[p]) v = v ^ m) :
    (∀ v : G, Q 0 v = 1) ∧
      (∀ v : G, Q 1 v = v) ∧
      (∀ a : ℤ_[p], Q a 1 = 1) ∧
      (∀ (a b : ℤ_[p]) (v : G), Q (a + b) v = Q a v * Q b v) ∧
      (∀ (a b : ℤ_[p]) (v : G), Q (a * b) v = Q b (Q a v)) ∧
      (∀ (a : ℤ_[p]) (v w : G), Q a (v * w) = Q a v * Q a w) := by
  have hscalar (v : G) : Continuous (fun a : ℤ_[p] => Q a v) :=
    hQ.comp (continuous_id.prodMk continuous_const)
  have hd : DenseRange (Int.cast : ℤ → ℤ_[p]) := PadicInt.denseRange_intCast
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    simpa only [Int.cast_zero, zpow_zero] using hQint 0 v
  · intro v
    simpa only [Int.cast_one, zpow_one] using hQint 1 v
  · intro a
    have heq : (fun b : ℤ_[p] => Q b 1) = fun _ => (1 : G) := by
      apply hd.equalizer (hscalar 1) continuous_const
      funext m
      exact (hQint m 1).trans (one_zpow m)
    exact congrFun heq a
  · intro a b v
    have heq : (fun t : ℤ_[p] × ℤ_[p] => Q (t.1 + t.2) v) =
        fun t => Q t.1 v * Q t.2 v := by
      apply (hd.prodMap hd).equalizer
      · exact (hscalar v).comp (continuous_fst.add continuous_snd)
      · exact ((hscalar v).comp continuous_fst).mul ((hscalar v).comp continuous_snd)
      · funext t
        change Q ((t.1 : ℤ_[p]) + (t.2 : ℤ_[p])) v =
          Q (t.1 : ℤ_[p]) v * Q (t.2 : ℤ_[p]) v
        rw [← Int.cast_add, hQint, hQint, hQint, zpow_add]
    exact congrFun heq (a, b)
  · intro a b v
    have heq : (fun t : ℤ_[p] × ℤ_[p] => Q (t.1 * t.2) v) =
        fun t => Q t.2 (Q t.1 v) := by
      apply (hd.prodMap hd).equalizer
      · exact (hscalar v).comp (continuous_fst.mul continuous_snd)
      · exact hQ.comp (continuous_snd.prodMk ((hscalar v).comp continuous_fst))
      · funext t
        change Q ((t.1 : ℤ_[p]) * (t.2 : ℤ_[p])) v =
          Q (t.2 : ℤ_[p]) (Q (t.1 : ℤ_[p]) v)
        rw [← Int.cast_mul, hQint, hQint, hQint, zpow_mul]
    exact congrFun heq (a, b)
  · intro a v w
    have heq : (fun b : ℤ_[p] => Q b (v * w)) = fun b => Q b v * Q b w := by
      apply hd.equalizer (hscalar (v * w)) ((hscalar v).mul (hscalar w))
      funext m
      change Q (m : ℤ_[p]) (v * w) = Q (m : ℤ_[p]) v * Q (m : ℤ_[p]) w
      rw [hQint, hQint, hQint, mul_zpow]
    exact congrFun heq a

namespace Ideal

variable {R : Type u} [CommRing R]

/-- A unit reduces to one modulo `I` exactly when its difference from one belongs to `I`. -/
theorem mem_ker_unitsMap_quotient_iff (I : Ideal R) (v : Rˣ) :
    v ∈ (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker ↔ (v : R) - 1 ∈ I := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  exact Ideal.Quotient.mk_eq_one_iff_sub_mem (I := I) (v : R)

/-- The stock power congruence applied to the reduction kernel. The estimate is
uniform in the principal unit and does not require primality or completeness. -/
theorem pow_pow_sub_one_mem (I : Ideal R) {p : ℕ} (hpI : (p : R) ∈ I)
    (v : (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker) (n : ℕ) :
    (((v : Rˣ) : R) ^ p ^ n) - 1 ∈ I ^ (n + 1) := by
  have hv : ((v : Rˣ) : R) ≡ 1 [SMOD I] :=
    SModEq.sub_mem.mpr ((I.mem_ker_unitsMap_quotient_iff v).mp v.property)
  simpa only [one_pow] using SModEq.sub_mem.mp (hv.pow_pow_add_one hpI n)

/-- Powers of an element congruent to one, along the natural approximations to a
`p`-adic exponent, have a ring-valued limit modulo every power of `I`. -/
private theorem exists_pow_appr_smodEq (I : Ideal R) [IsPrecomplete I R]
    {p : ℕ} [Fact p.Prime] (hpI : (p : R) ∈ I) (a : ℤ_[p]) (x : R)
    (hx : x - 1 ∈ I) :
    ∃ L : R, ∀ n : ℕ, x ^ a.appr n ≡ L [SMOD I ^ n] := by
  suffices ∃ L : R, ∀ n : ℕ,
      x ^ a.appr n ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] by
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using this
  refine IsPrecomplete.prec' (I := I) (fun n => x ^ a.appr n) ?_
  intro m n hmn
  simp only [Ideal.smul_eq_mul, Ideal.mul_top]
  have hpow : x ^ p ^ m ≡ 1 [SMOD I ^ m] := by
    apply SModEq.mono (Ideal.pow_le_pow_right (Nat.le_succ m))
    simpa only [one_pow] using (SModEq.sub_mem.mpr hx).pow_pow_add_one hpI m
  obtain ⟨k, hk⟩ := a.dvd_appr_sub_appr m n hmn
  rw [← Nat.sub_add_cancel (a.appr_mono hmn), hk, pow_add, pow_mul]
  simpa only [one_pow, one_mul] using
    ((SModEq.pow k hpow).mul (SModEq.refl (x ^ a.appr m))).symm

private theorem continuous_of_pow_appr_congr {R : Type u} [CommRing R]
    [TopologicalSpace R] (I : Ideal R) (p : ℕ) [Fact p.Prime] (hI : IsAdic I)
    (F : ℤ_[p] × (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker → R)
    (hF : ∀ a v n, F (a, v) ≡ ((v : Rˣ) : R) ^ a.appr n [SMOD I ^ n]) :
    Continuous F := by
  rw [continuous_iff_continuousAt]
  intro t
  change Tendsto F (𝓝 t) (𝓝 (F t))
  rw [(hI.hasBasis_nhds (F t)).tendsto_right_iff]
  intro n _
  -- The bounded representative of reduction modulo `p ^ n` is locally constant.
  have ha : ∀ᶠ a : ℤ_[p] in 𝓝 t.1, a.appr n = t.1.appr n := by
    have hpos : 0 < (p : ℝ) ^ (-(n : ℤ)) :=
      zpow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) _
    filter_upwards [Metric.ball_mem_nhds t.1 hpos] with a ha
    have hm : PadicInt.toZModPow n a = PadicInt.toZModPow n t.1 := by
      rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
        ← PadicInt.norm_le_pow_iff_mem_span_pow]
      exact le_of_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using ha)
    have hval (b : ℤ_[p]) : (PadicInt.toZModPow n b).val = b.appr n := by
      change (b.appr n : ZMod (p ^ n)).val = b.appr n
      exact ZMod.val_natCast_of_lt (b.appr_lt n)
    exact (hval a).symm.trans ((congrArg ZMod.val hm).trans (hval t.1))
  have hval : Continuous (fun v : (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker =>
      ((v : Rˣ) : R)) :=
    Units.continuous_val.comp continuous_subtype_val
  have hv := (hI.hasBasis_nhds (((t.2 : Rˣ) : R))).tendsto_right_iff.mp
    ((hval.comp continuous_snd).tendsto t) n trivial
  filter_upwards [(continuous_fst.tendsto t).eventually ha, hv] with s hs hv
  rcases hv with ⟨r, hr, hv⟩
  change ((t.2 : Rˣ) : R) + r = ((s.2 : Rˣ) : R) at hv
  have hvs : ((s.2 : Rˣ) : R) ≡ ((t.2 : Rˣ) : R) [SMOD I ^ n] := by
    apply SModEq.sub_mem.mpr
    rw [← hv, add_sub_cancel_left]
    exact hr
  have hp : ((s.2 : Rˣ) : R) ^ s.1.appr n ≡
      ((t.2 : Rˣ) : R) ^ t.1.appr n [SMOD I ^ n] := by
    rw [hs]
    exact SModEq.pow _ hvs
  have hFs : F s ≡ F t [SMOD I ^ n] :=
    (hF s.1 s.2 n).trans (hp.trans (hF t.1 t.2 n).symm)
  exact ⟨F s - F t, SModEq.sub_mem.mp hFs, by
    simpa only [add_comm] using sub_add_cancel (F s) (F t)⟩

private theorem continuous_units_of_pow_appr_congr {R : Type u} [CommRing R]
    [TopologicalSpace R] (I : Ideal R) [IsAdicComplete I R]
    (p : ℕ) [Fact p.Prime] (hI : IsAdic I)
    (Q : ℤ_[p] → (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker →
      (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker)
    (hQ : ∀ a v n, ((Q a v : Rˣ) : R) ≡
      ((v : Rˣ) : R) ^ a.appr n [SMOD I ^ n]) :
    Continuous (fun t : ℤ_[p] × (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker =>
      Q t.1 t.2) := by
  let : IsTopologicalRing R := by
    rw [hI]
    infer_instance
  let : IsOpenUnits R :=
    IsOpenUnits.of_isAdic hI (IsAdicComplete.le_jacobson_bot I)
  have hval : Topology.IsEmbedding
      (fun v : (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker => ((v : Rˣ) : R)) :=
    IsOpenUnits.isOpenEmbedding_unitsVal.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  exact hval.continuous_iff.mpr
    (continuous_of_pow_appr_congr I p hI (fun t => ((Q t.1 t.2 : Rˣ) : R)) hQ)

/-- Canonical `p`-adic powers in the kernel of reduction modulo `I`.
This generalizes the powering construction of Fesenko–Vostokov I (6.1) from
valuation integers to complete adic commutative rings containing `p` in `I`. -/
@[no_expose]
noncomputable def padicPow {R : Type u} [CommRing R]
    (I : Ideal R) [IsAdicComplete I R]
    (p : ℕ) [Fact p.Prime] (hpI : (p : R) ∈ I) :
    ℤ_[p] → (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker →
      (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker := by
  classical
  intro a v
  have hv : ((v : Rˣ) : R) - 1 ∈ I :=
    (I.mem_ker_unitsMap_quotient_iff v).mp v.property
  have h : ∃ L : R, ∀ n : ℕ, (((v : Rˣ) : R) ^ a.appr n) ≡ L [SMOD I ^ n] := by
    exact exists_pow_appr_smodEq I hpI a (((v : Rˣ) : R)) hv
  let L : R := Classical.choose h
  have hL : ∀ n : ℕ, (((v : Rˣ) : R) ^ a.appr n) ≡ L [SMOD I ^ n] :=
    Classical.choose_spec h
  have hL1 : L - 1 ∈ I := by
    have hvpow : (((v : Rˣ) : R) ^ a.appr 1) ≡ 1 [SMOD I] := by
      simpa only [one_pow] using SModEq.pow (a.appr 1) (SModEq.sub_mem.mpr hv)
    have hLmod : (((v : Rˣ) : R) ^ a.appr 1) ≡ L [SMOD I] := by
      simpa only [pow_one] using hL 1
    exact SModEq.sub_mem.mp (hLmod.symm.trans hvpow)
  have hunit : IsUnit L :=
    Ideal.isUnit_of_sub_one_mem_jacobson_bot L (IsAdicComplete.le_jacobson_bot I hL1)
  exact ⟨hunit.unit, (I.mem_ker_unitsMap_quotient_iff hunit.unit).mpr
    (by simpa only [IsUnit.unit_spec] using hL1)⟩

variable (I : Ideal R) [IsAdicComplete I R]
variable (p : ℕ) [Fact p.Prime] (hpI : (p : R) ∈ I)

local notation "K" => MonoidHom.ker (Units.map (RingHom.toMonoidHom (Ideal.Quotient.mk I)))

/-- A `p`-adic power is congruent to the corresponding natural approximation power
modulo every power of the ideal. -/
theorem padicPow_smodEq_pow_appr (a : ℤ_[p]) (v : K) (n : ℕ) :
    (((I.padicPow p hpI a v : Rˣ) : R)) ≡
      (((v : Rˣ) : R) ^ a.appr n) [SMOD I ^ n] := by
  exact (Classical.choose_spec (exists_pow_appr_smodEq I hpI a (((v : Rˣ) : R))
    ((I.mem_ker_unitsMap_quotient_iff v).mp v.property)) n).symm

/-- The p-adic powers agree with every integer power, including negative powers. -/
theorem padicPow_intCast (n : ℤ) (v : K) :
    I.padicPow p hpI (n : ℤ_[p]) v = v ^ n := by
  apply Subtype.ext
  apply Units.ext
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro k
  simp only [Ideal.smul_eq_mul, Ideal.mul_top]
  refine (I.padicPow_smodEq_pow_appr p hpI (n : ℤ_[p]) v k).trans ?_
  let q := Ideal.Quotient.mk (I ^ k)
  let w : (R ⧸ I ^ k)ˣ := Units.map q.toMonoidHom (v : Rˣ)
  have hw : w ^ p ^ k = 1 := by
    apply Units.ext
    change q (((v : Rˣ) : R) ^ p ^ k) = 1
    apply (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr
    exact Ideal.pow_le_pow_right (Nat.le_succ k) (I.pow_pow_sub_one_mem hpI v k)
  have hcast : (((n : ℤ_[p]).appr k : ℕ) : ZMod (p ^ k)) = (n : ZMod (p ^ k)) :=
    map_intCast (PadicInt.toZModPow k) n
  have hmod : (((n : ℤ_[p]).appr k : ℕ) : ℤ) % (p ^ k : ℕ) = n % (p ^ k : ℕ) :=
    (ZMod.intCast_eq_intCast_iff' _ _ _).mp (by simpa only [Int.cast_natCast] using hcast)
  have hpow : w ^ (n : ℤ_[p]).appr k = w ^ n := by
    calc
      _ = w ^ (((n : ℤ_[p]).appr k : ℕ) : ℤ) := (zpow_natCast _ _).symm
      _ = w ^ ((((n : ℤ_[p]).appr k : ℕ) : ℤ) % (p ^ k : ℕ)) :=
        zpow_eq_zpow_emod' _ hw
      _ = w ^ (n % (p ^ k : ℕ)) := by rw [hmod]
      _ = w ^ n := (zpow_eq_zpow_emod' n hw).symm
  apply SModEq.idealQuotientMk.mpr
  change q (((v : Rˣ) : R) ^ (n : ℤ_[p]).appr k) =
    q (((v : Rˣ) ^ n : Rˣ) : R)
  simpa only [w, ← map_pow, ← map_zpow, Units.coe_map, Units.val_pow_eq_pow_val,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    using congrArg (fun z : (R ⧸ I ^ k)ˣ => (z : R ⧸ I ^ k)) hpow

private theorem padicPow_laws :
    (∀ v : K, I.padicPow p hpI 0 v = 1) ∧
      (∀ v : K, I.padicPow p hpI 1 v = v) ∧
      (∀ a : ℤ_[p], I.padicPow p hpI a 1 = 1) ∧
      (∀ (a b : ℤ_[p]) (v : K), I.padicPow p hpI (a + b) v =
        I.padicPow p hpI a v * I.padicPow p hpI b v) ∧
      (∀ (a b : ℤ_[p]) (v : K), I.padicPow p hpI (a * b) v =
        I.padicPow p hpI b (I.padicPow p hpI a v)) ∧
      (∀ (a : ℤ_[p]) (v w : K), I.padicPow p hpI a (v * w) =
        I.padicPow p hpI a v * I.padicPow p hpI a w) := by
  let : TopologicalSpace R := I.adicTopology
  let : IsTopologicalRing R := I.ringFilterBasis.isTopologicalRing
  have hI : IsAdic I := rfl
  let : T2Space R := hI.isHausdorff_iff.mp inferInstance
  exact padicPower_laws_of_continuous_of_intCast (I.padicPow p hpI)
    (continuous_units_of_pow_appr_congr I p hI (I.padicPow p hpI)
      (I.padicPow_smodEq_pow_appr p hpI))
    (I.padicPow_intCast p hpI)

/-- Addition of exponents becomes multiplication of principal units. -/
theorem padicPow_add (a b : ℤ_[p]) (v : K) :
    I.padicPow p hpI (a + b) v =
      I.padicPow p hpI a v * I.padicPow p hpI b v := by
  exact (I.padicPow_laws p hpI).2.2.2.1 a b v

/-- Multiplication of exponents agrees with iterated powering. -/
theorem padicPow_mul (a b : ℤ_[p]) (v : K) :
    I.padicPow p hpI (a * b) v =
      I.padicPow p hpI b (I.padicPow p hpI a v) := by
  exact (I.padicPow_laws p hpI).2.2.2.2.1 a b v

/-- A p-adic power preserves products of principal units. -/
theorem padicPow_mul_units (a : ℤ_[p]) (v w : K) :
    I.padicPow p hpI a (v * w) =
      I.padicPow p hpI a v * I.padicPow p hpI a w := by
  exact (I.padicPow_laws p hpI).2.2.2.2.2 a v w

/-- The zeroth power is one. -/
@[simp] theorem padicPow_zero (v : K) : I.padicPow p hpI 0 v = 1 := by
  exact (I.padicPow_laws p hpI).1 v

/-- The first power is the original principal unit. -/
@[simp] theorem padicPow_one (v : K) : I.padicPow p hpI 1 v = v := by
  exact (I.padicPow_laws p hpI).2.1 v

/-- Every p-adic power of the unit element is the unit element. -/
@[simp] theorem padicPow_unit_one (a : ℤ_[p]) : I.padicPow p hpI a 1 = 1 := by
  exact (I.padicPow_laws p hpI).2.2.1 a

/-- The `ℤ_[p]`-module on the additive form of the reduction kernel, with scalar
operation given by p-adic powering. This is the module of Fesenko–Vostokov
I (6.1), generalized to complete adic rings. It is not a global instance. -/
@[instance_reducible]
noncomputable def padicModule : Module ℤ_[p] (Additive K) where
  smul a v := Additive.ofMul (I.padicPow p hpI a v.toMul)
  one_smul v :=
    congrArg Additive.ofMul (I.padicPow_one (p := p) (hpI := hpI) v.toMul)
  mul_smul a b v :=
    congrArg Additive.ofMul
      ((congrArg (fun c => I.padicPow p hpI c v.toMul) (mul_comm a b)).trans
        (I.padicPow_mul p hpI b a v.toMul))
  smul_zero a :=
    congrArg Additive.ofMul (I.padicPow_unit_one (p := p) (hpI := hpI) a)
  smul_add a v w :=
    congrArg Additive.ofMul
      (I.padicPow_mul_units (p := p) (hpI := hpI) a v.toMul w.toMul)
  add_smul a b v :=
    congrArg Additive.ofMul (I.padicPow_add (p := p) (hpI := hpI) a b v.toMul)
  zero_smul v :=
    congrArg Additive.ofMul (I.padicPow_zero (p := p) (hpI := hpI) v.toMul)

/-- Evaluation of the scalar operation of `padicModule` is p-adic powering. -/
theorem padicModule_smul (a : ℤ_[p]) (v : K) :
    @SMul.smul ℤ_[p] (Additive K) (I.padicModule p hpI).toSMul a (Additive.ofMul v) =
      Additive.ofMul (I.padicPow p hpI a v) := rfl

variable [TopologicalSpace R]

/-- Joint continuity of the powering map, as in Fesenko–Vostokov I (6.1). -/
theorem continuous_padicPow (hI : IsAdic I) :
    Continuous (fun t : ℤ_[p] × K => I.padicPow p hpI t.1 t.2) := by
  exact continuous_units_of_pow_appr_congr I p hI (I.padicPow p hpI)
    (I.padicPow_smodEq_pow_appr p hpI)

/-- Integer approximations to an exponent give the limit defining its continuous power,
as in Fesenko–Vostokov I (6.1). -/
theorem tendsto_zpow_padicPow (hI : IsAdic I) (v : K) (a : ℤ_[p]) (n : ℕ → ℤ)
    (hn : Tendsto (fun k => (n k : ℤ_[p])) atTop (𝓝 a)) :
    Tendsto (fun k => v ^ n k) atTop (𝓝 (I.padicPow p hpI a v)) := by
  have hlim := ((I.continuous_padicPow (p := p) (hpI := hpI) hI).tendsto (a, v)).comp
    (hn.prodMk_nhds tendsto_const_nhds)
  simpa only [Function.comp_def, padicPow_intCast] using hlim

/-- Integer powers characterize the extension uniquely; continuity in the exponent
for each fixed principal unit already suffices. -/
theorem padicPow_unique (hI : IsAdic I) (Q : ℤ_[p] → K → K)
    (hQ : ∀ v, Continuous (fun a => Q a v))
    (hQint : ∀ (n : ℤ) (v : K), Q (n : ℤ_[p]) v = v ^ n) :
    Q = I.padicPow p hpI := by
  let : T2Space R := hI.isHausdorff_iff.mp inferInstance
  funext a v
  have heq : (fun b : ℤ_[p] => Q b v) = fun b => I.padicPow p hpI b v := by
    apply PadicInt.denseRange_intCast.equalizer (hQ v)
      ((I.continuous_padicPow p hpI hI).comp (continuous_id.prodMk continuous_const))
    funext n
    exact (hQint n v).trans (I.padicPow_intCast p hpI n v).symm
  exact congrFun heq a

/-- The explicitly supplied module structure has jointly continuous scalar multiplication. -/
theorem continuousSMul_padicModule (hI : IsAdic I) :
    @ContinuousSMul ℤ_[p] (Additive K) (I.padicModule p hpI).toSMul
      inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ_[p] (Additive K) (I.padicModule p hpI).toSMul
    inferInstance inferInstance (I.continuous_padicPow p hpI hI)

end Ideal

/-- Raising principal units of a Henselian pair to the `n`-th power is bijective
when `n` is a unit in the residue quotient. The principal units are the kernel of
reduction on units, with their existing subgroup powers. No topology or positivity
assumption on `n` is required. -/
theorem HenselianRing.bijective_pow_principal_units {R : Type u} [CommRing R]
    (I : Ideal R) [HenselianRing R I] (n : ℕ) (hn : IsUnit (n : R ⧸ I)) :
    Function.Bijective
      (fun u : (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker => u ^ n) := by
  classical
  letI : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot I (HenselianRing.jac (R := R) (I := I))
  have hquot (u : (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker) :
      Ideal.Quotient.mk I ((u : Rˣ) : R) = 1 :=
    (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr
      ((Ideal.mem_ker_unitsMap_quotient_iff I (u : Rˣ)).mp u.property)
  constructor
  · intro u v huv
    have hp := congrArg
      (fun w : (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker => ((w : Rˣ) : R)) huv
    change ((u : Rˣ) : R) ^ n = ((v : Rˣ) : R) ^ n at hp
    -- The power-difference factor reduces to the unit exponent in the quotient.
    let s : R := (Finset.range n).sum fun i =>
      ((u : Rˣ) : R) ^ i * ((v : Rˣ) : R) ^ (n - 1 - i)
    have hs : Ideal.Quotient.mk I s = (n : R ⧸ I) := by
      dsimp only [s]
      rw [RingHom.map_geom_sum₂, hquot u, hquot v, geom_sum₂_self, one_pow, mul_one]
    have hsunit : IsUnit s := by
      apply IsUnit.of_map (Ideal.Quotient.mk I) s
      rwa [hs]
    have hzero : s * (((u : Rˣ) : R) - ((v : Rˣ) : R)) = 0 := by
      dsimp only [s]
      rw [geom_sum₂_mul, hp, sub_self]
    apply Subtype.ext
    apply Units.ext
    apply sub_eq_zero.mp
    exact hsunit.mul_left_cancel (hzero.trans (mul_zero s).symm)
  · intro u
    have hu : ((u : Rˣ) : R) - 1 ∈ I :=
      (Ideal.mem_ker_unitsMap_quotient_iff I (u : Rˣ)).mp u.property
    -- Nonmonic simple-root lifting also covers the zeroth exponent.
    obtain ⟨x, hx, hxI⟩ := HenselianRing.exists_root I
      (Polynomial.X ^ n - Polynomial.C ((u : Rˣ) : R)) 1
      (by
        simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
          one_pow, Polynomial.eval_C, neg_sub] using I.neg_mem hu)
      (by
        simpa only [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
          Polynomial.derivative_C, sub_zero, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_natCast, one_pow, mul_one,
          map_natCast] using hn)
    have hxpow : x ^ n = ((u : Rˣ) : R) := by
      simpa only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using hx
    have hxunit : IsUnit x := by
      apply IsUnit.of_map (Ideal.Quotient.mk I) x
      rw [(Ideal.Quotient.mk_eq_one_iff_sub_mem x).mpr hxI]
      exact isUnit_one
    refine ⟨⟨hxunit.unit, (Ideal.mem_ker_unitsMap_quotient_iff I _).mpr ?_⟩, ?_⟩
    · simpa only [hxunit.unit_spec] using hxI
    · apply Subtype.ext
      apply Units.ext
      change (hxunit.unit : R) ^ n = ((u : Rˣ) : R)
      simpa only [hxunit.unit_spec] using hxpow
