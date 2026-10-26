/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Teichmuller
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.CharP.Algebra

/-!
# Teichmüller sections of surjective residue maps

For a surjective ring map `f : R →+* κ` with perfect characteristic-`p` codomain,
`RingHom.teichmullerSection` is the canonical multiplicative section when `R` is
complete for the powers of `ker f`. It is the composite of `Perfection.lift` with
Mathlib's `Perfection.teichmuller₀`, not a separate limit construction.

The reduction, inverse-Frobenius congruence and uniqueness laws characterize the
section without a topology or continuity assumption. In characteristic `p` on `R`
it is the underlying function of a ring homomorphism. Perfectness of `R` is not needed.

The section's image is the intersection of all `p^n`-power images in `R`.
Membership is equivalent to the separate existence of a `p^n`-th root at each
depth, including zero and `n = 0`; no compatible root tower is assumed. This
follows from the reduced-residue image theorem below and Mathlib's universal
property of the perfection.

## Scope

The construction and its proofs use algebraic adic completeness; no topology
is chosen. The ideal-based image theorem below also applies to imperfect
reduced residue rings, without constructing a section on the whole residue ring.

## References

* Mathlib's `Mathlib/RingTheory/Teichmuller.lean` and
  `Mathlib/RingTheory/Perfection.lean` (Kenny Lau), for the complete ideal-based
  construction, its approximation API and the perfection's universal property.
* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second
  edition, I §7, (7.1) and (7.3), for the image characterization and the
  perfect-residue and equal-characteristic corollaries.
-/

@[expose] public section

universe u v

namespace Perfection

/-- Coefficients of the perfection lift are images of iterated inverse-Frobenius roots. -/
@[simp]
theorem coeff_lift (p : ℕ) [Fact p.Prime] {A : Type u} {B : Type v}
    [CommSemiring A] [CommSemiring B] [CharP A p] [PerfectRing A p] [CharP B p]
    (f : A →+* B) (a : A) (n : ℕ) :
    coeff B p n ((lift p A B) f a) = f (((frobeniusEquiv A p).symm)^[n] a) := rfl

variable (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R]
    (I : Ideal R) [CharP (R ⧸ I) p] [IsAdicComplete I R]

/-- In equal characteristic, the ideal-based Teichmüller map is additive.
This is the characteristic-`p` refinement of the stock multiplicative map. -/
theorem teichmuller₀_map_add [CharP R p] (x y : Perfection (R ⧸ I) p) :
    teichmuller₀ p I (x + y) = teichmuller₀ p I x + teichmuller₀ p I y := by
  refine teichmuller₀_spec fun n ↦ ?_
  refine ⟨(coeff _ p n x).out + (coeff _ p n y).out, by simp, ?_⟩
  rw [add_pow_char_pow]
  exact (teichmuller₀_sModEq (Ideal.Quotient.mk_out _)).symm.add
    (teichmuller₀_sModEq (Ideal.Quotient.mk_out _)).symm

/-- The stock Teichmüller map as a ring homomorphism in equal characteristic.
Its underlying function is unchanged. -/
noncomputable def teichmullerRingHom [CharP R p] : Perfection (R ⧸ I) p →+* R where
  __ := teichmuller₀ p I
  map_add' := teichmuller₀_map_add p I

@[simp]
theorem teichmullerRingHom_apply [CharP R p] (x : Perfection (R ⧸ I) p) :
    teichmullerRingHom p I x = teichmuller₀ p I x := rfl

@[simp]
theorem mk_teichmullerRingHom [CharP R p] (x : Perfection (R ⧸ I) p) :
    Ideal.Quotient.mk I (teichmullerRingHom p I x) = coeff _ p 0 x :=
  mk_teichmuller₀ x

end Perfection

namespace RingHom

variable (p : ℕ) [Fact p.Prime] {R : Type u} {κ : Type v}
    [CommRing R] [CommRing κ] [CharP κ p] [PerfectRing κ p]
    (f : R →+* κ) (hf : Function.Surjective f) [IsAdicComplete (ker f) R]

/-- The canonical multiplicative section of a surjective map to a perfect
characteristic-`p` ring, for a ring complete along the map's kernel.
It lifts inverse-Frobenius sequences through the quotient by `ker f` and then
applies `Perfection.teichmuller₀`. -/
noncomputable def teichmullerSection : κ →*₀ R := by
  let e := f.quotientKerEquivOfSurjective hf
  letI : CharP (R ⧸ ker f) p :=
    charP_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective p
  exact (Perfection.teichmuller₀ p (ker f)).comp
    ((Perfection.lift p κ (R ⧸ ker f)) e.symm.toRingHom).toMonoidWithZeroHom

-- Keep the quotient implementation available without unfolding the section in its laws.
private theorem teichmullerSection_eq_comp [CharP (R ⧸ ker f) p] :
    teichmullerSection p f hf = (Perfection.teichmuller₀ p (ker f)).comp
      ((Perfection.lift p κ (R ⧸ ker f))
        (f.quotientKerEquivOfSurjective hf).symm.toRingHom).toMonoidWithZeroHom := rfl

/-- Reduction of the Teichmüller section is the identity. -/
@[simp]
theorem teichmullerSection_reduction_apply (a : κ) :
    f (teichmullerSection p f hf a) = a := by
  let e := f.quotientKerEquivOfSurjective hf
  let : CharP (R ⧸ ker f) p :=
    charP_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective p
  rw [teichmullerSection_eq_comp]
  change e (Ideal.Quotient.mk (ker f)
    (Perfection.teichmuller₀ p (ker f)
      ((Perfection.lift p κ (R ⧸ ker f)) e.symm.toRingHom a))) = a
  rw [Perfection.mk_teichmuller₀, Perfection.coeff_lift]
  exact e.apply_symm_apply a

/-- The section law as an equality of multiplicative maps with zero. -/
@[simp]
theorem comp_teichmullerSection :
    f.toMonoidWithZeroHom.comp (teichmullerSection p f hf) =
      MonoidWithZeroHom.id κ := by
  ext a
  exact teichmullerSection_reduction_apply p f hf a

/-- A Teichmüller section is injective, since reduction is a left inverse. -/
theorem teichmullerSection_injective : Function.Injective (teichmullerSection p f hf) := by
  intro a b hab
  simpa only [teichmullerSection_reduction_apply] using congrArg f hab

/-- The inverse-Frobenius approximation law, including `n = 0` and `a = 0`.
Every lift of the `n`-th inverse-Frobenius root gives the same approximation
modulo the `(n + 1)`-st power of the kernel. -/
theorem teichmullerSection_sModEq (a : κ) (r : R) (n : ℕ)
    (hr : f r = ((frobeniusEquiv κ p).symm)^[n] a) :
    teichmullerSection p f hf a ≡ r ^ (p ^ n) [SMOD (ker f) ^ (n + 1)] := by
  let e := f.quotientKerEquivOfSurjective hf
  let : CharP (R ⧸ ker f) p :=
    charP_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective p
  rw [teichmullerSection_eq_comp]
  apply Perfection.teichmuller₀_sModEq
  simp only [RingHom.toMonoidWithZeroHom_eq_coe]
  rw [Perfection.coeff_lift, ← hr]
  exact (quotientKerEquivOfSurjective_symm_apply hf r).symm

/-- Any multiplicative section preserving zero and one agrees with the
Teichmüller section. No continuity hypothesis is needed. This is the uniqueness
in the perfect-residue corollary of Fesenko–Vostokov, I §7, (7.3). -/
theorem teichmullerSection_unique (s : κ →*₀ R) (hs : ∀ a, f (s a) = a) :
    s = teichmullerSection p f hf := by
  ext a
  symm
  refine (IsHausdorff.eq_iff_smodEq (I := ker f)).mpr fun n ↦ ?_
  rw [smul_eq_mul, Ideal.mul_top]
  -- Multiplicativity turns the lifted inverse-Frobenius roots into approximations to `s a`.
  have h := teichmullerSection_sModEq p f hf a
    (s (((frobeniusEquiv κ p).symm)^[n] a)) n (hs _)
  rw [← map_pow, iterate_frobeniusEquiv_symm_pow_p_pow] at h
  exact h.mono (Ideal.pow_le_pow_right (Nat.le_succ n))

/-- Application form of the universal property. -/
theorem teichmullerSection_unique_apply (s : κ →*₀ R) (hs : ∀ a, f (s a) = a) (a : κ) :
    s a = teichmullerSection p f hf a :=
  DFunLike.congr_fun (teichmullerSection_unique p f hf s hs) a

section EqualCharacteristic
variable [CharP R p]

/-- The Teichmüller section packaged as a ring map in equal characteristic.
This composes the equal-characteristic refinement of the stock map with the
same perfection lift used by `teichmullerSection`. -/
noncomputable def teichmullerSectionRingHom : κ →+* R := by
  let e := f.quotientKerEquivOfSurjective hf
  letI : CharP (R ⧸ ker f) p :=
    charP_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective p
  exact (Perfection.teichmullerRingHom p (ker f)).comp
    ((Perfection.lift p κ (R ⧸ ker f)) e.symm.toRingHom)

/-- The ring refinement has the same underlying function. -/
@[simp]
theorem teichmullerSectionRingHom_apply (a : κ) :
    teichmullerSectionRingHom p f hf a = teichmullerSection p f hf a := rfl

/-- The ring refinement reduces to the identity. -/
@[simp]
theorem teichmullerSectionRingHom_reduction_apply (a : κ) :
    f (teichmullerSectionRingHom p f hf a) = a :=
  teichmullerSection_reduction_apply p f hf a

/-- Equal-characteristic additivity of the same multiplicative section.
This is the perfect-residue specialization of I §7, (7.3), Corollary 2. -/
theorem teichmullerSection_map_add (a b : κ) :
    teichmullerSection p f hf (a + b) =
      teichmullerSection p f hf a + teichmullerSection p f hf b :=
  map_add (teichmullerSectionRingHom p f hf) a b

end EqualCharacteristic

section Field
variable {k : Type v} [Field k] [CharP k p] [PerfectRing k p]
    (g : R →+* k) (hg : Function.Surjective g) [IsAdicComplete (ker g) R]

/-- Over a residue field, a nonzero residue has a unit representative.
For arbitrary perfect residue rings, nonzero elements need not be units. -/
theorem isUnit_teichmullerSection {a : k} (ha : a ≠ 0) :
    IsUnit (teichmullerSection p g hg a) :=
  IsUnit.map (teichmullerSection p g hg) (isUnit_iff_ne_zero.mpr ha)

end Field

section Quotient
variable (I : Ideal R) [CharP (R ⧸ I) p] [PerfectRing (R ⧸ I) p]
    [IsAdicComplete I R]

/-- In the quotient presentation, the section is the stock Teichmüller map
composed with the perfection lift of the identity. This agreement lemma avoids
a second ideal-based section construction. -/
theorem teichmullerSection_quotient_apply (a : R ⧸ I) :
    @teichmullerSection p _ R (R ⧸ I) _ _ _ _ (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
      (by simpa only [Ideal.mk_ker] using (inferInstance : IsAdicComplete I R)) a =
      Perfection.teichmuller₀ p I
        ((Perfection.lift p (R ⧸ I) (R ⧸ I)) (RingHom.id _) a) := by
  let : IsAdicComplete (ker (Ideal.Quotient.mk I)) R := by
    simpa only [Ideal.mk_ker] using (inferInstance : IsAdicComplete I R)
  let s := (Perfection.teichmuller₀ p I).comp
    ((Perfection.lift p (R ⧸ I) (R ⧸ I)) (RingHom.id _)).toMonoidWithZeroHom
  exact (teichmullerSection_unique_apply p (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective s (fun b ↦ by
      change Ideal.Quotient.mk I (Perfection.teichmuller₀ p I _) = b
      rw [Perfection.mk_teichmuller₀]
      simp only [RingHom.toMonoidWithZeroHom_eq_coe, Perfection.coeff_lift]
      rfl) a).symm

end Quotient

end RingHom

/-!
## Image of the perfection in a complete ring

For reduced characteristic-`p` residue rings, the stock ideal-based Teichmüller
map is injective and its image is the intersection of all `p^n`-power images in
`R`. In the reverse inclusion, the roots may be chosen separately for each `n`;
a compatible root tower is not an additional hypothesis. Reducedness supplies
injectivity of the residue Frobenius, not surjectivity.

This is the adic-ring form of the perfect-core characterization in
Fesenko–Vostokov, *Local Fields and Their Extensions*, second edition, I §7,
(7.1). It does not require perfect residue, a field, or a topology. The map is
Mathlib's `Perfection.teichmuller₀`, with its existing `quotientMulEquiv` and
coefficient recovery API; no new perfection or limit construction is used.
-/

namespace Perfection

section ReducedResidue

variable (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R]
    (I : Ideal R) [CharP (R ⧸ I) p] [IsAdicComplete I R] [IsReduced (R ⧸ I)]

/-- The Teichmüller map from the perfection of a reduced residue ring is
injective. Residue Frobenius need not be surjective. This generalizes the
uniqueness in Fesenko–Vostokov, I §7, (7.1), to complete adic rings. -/
theorem teichmuller₀_injective : Function.Injective (teichmuller₀ p I) := by
  intro x y hxy
  have hzero : coeff (R ⧸ I) p 0 x = coeff (R ⧸ I) p 0 y := by
    simpa only [mk_teichmuller₀] using congrArg (Ideal.Quotient.mk I) hxy
  apply Perfection.ext
  intro n
  apply iterateFrobenius_inj (R ⧸ I) p n
  change coeffMonoidHom (R ⧸ I) p n x ^ (p ^ n) =
    coeffMonoidHom (R ⧸ I) p n y ^ (p ^ n)
  rw [coeffMonoidHom_pow_p_pow_self, coeffMonoidHom_pow_p_pow_self]
  simpa only [coeffMonoidHom_eq_coeff] using hzero

/-- The image of the Teichmüller map is the intersection of all `p^n`-power
images, including zero. The `n = 0` term is the whole ring. In particular,
separately existing roots suffice; no compatible tower is assumed.
This is the adic-ring form of Fesenko–Vostokov, I §7, (7.1). -/
theorem range_teichmuller₀ :
    Set.range (teichmuller₀ p I) = ⋂ n : ℕ, Set.range (fun r : R ↦ r ^ (p ^ n)) := by
  classical
  apply Set.Subset.antisymm
  · rintro _ ⟨a, rfl⟩
    refine Set.mem_iInter.mpr fun n ↦ ?_
    refine ⟨teichmuller₀ p I ((powMulEquiv _ (p ^ n)).symm a), ?_⟩
    change teichmuller₀ p I ((powMulEquiv _ (p ^ n)).symm a) ^ (p ^ n) =
      teichmuller₀ p I a
    rw [← map_pow, powMulEquiv_symm_pow_p]
  · intro x hx
    have hroots : ∀ n : ℕ, ∃ r : R, r ^ (p ^ n) = x := by
      simpa only [Set.mem_iInter, Set.mem_range] using hx
    choose r hr using hroots
    -- Reducedness makes the independently chosen residue roots compatible.
    let a : Perfection (R ⧸ I) p := ⟨fun n ↦ Ideal.Quotient.mk I (r n), fun n ↦ by
      apply iterateFrobenius_inj (R ⧸ I) p n
      change (Ideal.Quotient.mk I (r (n + 1)) ^ p) ^ (p ^ n) =
        Ideal.Quotient.mk I (r n) ^ (p ^ n)
      calc
        _ = Ideal.Quotient.mk I (r (n + 1) ^ (p ^ (n + 1))) := by
          rw [map_pow, pow_succ', pow_mul]
        _ = Ideal.Quotient.mk I x := congrArg (Ideal.Quotient.mk I) (hr (n + 1))
        _ = _ := by rw [← map_pow, hr n]⟩
    refine ⟨a, teichmuller₀_spec fun n ↦ ⟨r n, rfl, ?_⟩⟩
    rw [hr n]

/-- Membership in the Teichmüller image is equivalent to the existence of a
`p^n`-th root for each `n`, with no compatibility condition on the witnesses. -/
theorem mem_range_teichmuller₀_iff (x : R) :
    x ∈ Set.range (teichmuller₀ p I) ↔ ∀ n : ℕ, ∃ r : R, r ^ (p ^ n) = x := by
  rw [range_teichmuller₀ p I]
  simp only [Set.mem_iInter, Set.mem_range]

end ReducedResidue

end Perfection

namespace RingHom

variable (p : ℕ) [Fact p.Prime] {R : Type u} {κ : Type v}
    [CommRing R] [CommRing κ] [CharP κ p] [PerfectRing κ p]
    (f : R →+* κ) (hf : Function.Surjective f) [IsAdicComplete (ker f) R]

/-- The canonical Teichmüller section has image the intersection of all
`p^n`-power images, including zero and `n = 0`. No compatibility between root
witnesses is assumed. This follows from `Perfection.range_teichmuller₀`, the
adic-ring form of Fesenko–Vostokov, I §7, (7.1), and Mathlib's perfection
universal property. -/
theorem range_teichmullerSection :
    Set.range (teichmullerSection p f hf) =
      ⋂ n : ℕ, Set.range (fun r : R ↦ r ^ (p ^ n)) := by
  let B := R ⧸ ker f
  let e : B ≃+* κ := f.quotientKerEquivOfSurjective hf
  let : CharP B p :=
    charP_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective p
  -- Perfectness makes the residue reduced; no extra reducedness assumption is needed.
  let : IsReduced κ :=
    (isReduced_iff_pow_one_lt p (Fact.out : p.Prime).one_lt).mpr fun a ha ↦
      (injective_frobenius κ p) (ha.trans (map_zero (frobenius κ p)).symm)
  let : IsReduced B := isReduced_of_injective e.toRingHom e.injective
  let L : κ →+* Perfection B p := (Perfection.lift p κ B) e.symm.toRingHom
  -- Coefficient zero determines maps from a perfect ring into the perfection.
  have hright :
      L.comp (e.toRingHom.comp (Perfection.coeff B p 0)) =
        RingHom.id (Perfection B p) := by
    apply Perfection.hom_ext (p := p)
    intro y
    simpa only [L, RingHom.comp_apply, RingHom.id_apply,
      Perfection.coeff_lift, Function.iterate_zero, id_eq,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using
      e.symm_apply_apply (Perfection.coeff B p 0 y)
  have hL : Function.Surjective L := by
    intro y
    exact ⟨e (Perfection.coeff B p 0 y), DFunLike.congr_fun hright y⟩
  let s : κ →*₀ R := (Perfection.teichmuller₀ p (ker f)).comp L.toMonoidWithZeroHom
  have hs : ∀ a, f (s a) = a := by
    intro a
    calc
      f (s a) = e (Ideal.Quotient.mk (ker f) (s a)) :=
        (quotientKerEquivOfSurjective_apply_mk (f := f) hf (s a)).symm
      _ = e (Perfection.coeff B p 0 (L a)) :=
        congrArg e (Perfection.mk_teichmuller₀ (L a))
      _ = a := by
        simpa only [L, Perfection.coeff_lift, Function.iterate_zero, id_eq,
          RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using
          e.apply_symm_apply a
  have hsection : s = teichmullerSection p f hf :=
    teichmullerSection_unique p f hf s hs
  have hrange : Set.range (teichmullerSection p f hf) =
      Set.range (Perfection.teichmuller₀ p (ker f)) := by
    rw [← hsection]
    apply Set.Subset.antisymm
    · rintro _ ⟨a, rfl⟩
      exact ⟨L a, rfl⟩
    · rintro _ ⟨y, rfl⟩
      obtain ⟨a, ha⟩ := hL y
      exact ⟨a, congrArg (Perfection.teichmuller₀ p (ker f)) ha⟩
  exact hrange.trans (Perfection.range_teichmuller₀ p (ker f))

/-- Membership in the canonical Teichmüller image means that a `p^n`-th root
exists for every `n`. The witnesses need not form a compatible tower. -/
theorem mem_range_teichmullerSection_iff (x : R) :
    x ∈ Set.range (teichmullerSection p f hf) ↔
      ∀ n : ℕ, ∃ r : R, r ^ (p ^ n) = x := by
  rw [range_teichmullerSection p f hf]
  simp only [Set.mem_iInter, Set.mem_range]

end RingHom
