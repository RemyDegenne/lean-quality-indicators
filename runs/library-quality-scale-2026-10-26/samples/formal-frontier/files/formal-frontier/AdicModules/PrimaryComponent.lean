/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.Ideal.Int

/-!
# Exactness of primary components

Over a Dedekind domain, taking the component at a height-one prime preserves an
exact pair when its **source** is torsion. The result applies to arbitrary modules;
it does not require a uniform annihilating ideal power, finite generation, or
torsion of the middle or target module.

For abelian groups, the component of the integer ideal `(p)` is the usual
`p`-primary subgroup. We identify the carriers and the restricted homomorphisms
and transport exactness to maps of those ordinary subgroups.

## References

The lifting argument uses Mathlib's Dedekind ideal-primary-component
`map_surjective`, exactness and kernel corestriction APIs. The integer comparison
uses the canonical integer action and ordinary torsion/primary-subgroup APIs;
see `docs/PrimaryComponent.md` for the method and `docs/CREDITS.md` for the
distinct source-research and library-adaptation contributions.
-/

@[expose] public section

open Function IsDedekindDomain

namespace Ideal

variable {R M N Q : Type*} [CommRing R] [IsDedekindDomain R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q]
  [Module R M] [Module R N] [Module R Q]

/-- Restriction to a height-one primary component preserves exactness of a pair
whose source module is torsion. The other modules need not be torsion. -/
theorem primaryComponent.exact (hM : Module.IsTorsion R M)
    (prime : HeightOneSpectrum R) (f : M →ₗ[R] N) (g : N →ₗ[R] Q)
    (hfg : Function.Exact f g) :
    Function.Exact (primaryComponent.map prime.asIdeal f)
      (primaryComponent.map prime.asIdeal g) := by
  let toKernel : M →ₗ[R] g.ker :=
    f.codRestrict g.ker (fun m => (hfg (f m)).2 ⟨m, rfl⟩)
  have hSurj : Function.Surjective toKernel := by
    rintro ⟨n, hn⟩
    obtain ⟨m, hm⟩ := (hfg n).1 (by simpa using hn)
    exact ⟨m, Subtype.ext hm⟩
  intro n
  constructor
  · intro hn
    have hgn : g (n : N) = 0 := by
      have heq := congrArg
        (fun t : primaryComponent Q prime.asIdeal => (t : Q)) hn
      simpa [primaryComponent.map] using heq
    let nk : g.ker := ⟨n, by simpa using hgn⟩
    have hnk : nk ∈ primaryComponent g.ker prime.asIdeal := by
      obtain ⟨exponent, he⟩ :=
        (primaryComponent_mem (M := N) prime.asIdeal (n : N)).1 n.property
      apply (primaryComponent_mem (M := g.ker) prime.asIdeal nk).2
      refine ⟨exponent, ?_⟩
      rw [Submodule.mem_torsionBySet_iff] at he ⊢
      intro scalar
      apply Subtype.ext
      exact he scalar
    obtain ⟨m, hm⟩ :=
      (primaryComponent.map_surjective hM prime toKernel hSurj) ⟨nk, hnk⟩
    refine ⟨m, Subtype.ext ?_⟩
    have heq := congrArg
      (fun t : primaryComponent g.ker prime.asIdeal => (t : g.ker)) hm
    have heq' := congrArg (fun t : g.ker => (t : N)) heq
    change f (m : M) = (n : N) at heq'
    exact heq'
  · rintro ⟨m, rfl⟩
    apply Subtype.ext
    exact (hfg (f (m : M))).2 ⟨m, rfl⟩

end Ideal

namespace AddCommGroup

variable {G H K : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup K]

/-- The height-one prime ideal `(p)` in the integers, for a natural prime `p`. -/
def integerPrime (p : ℕ) [Fact p.Prime] : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(p : ℤ)}
  isPrime := (Int.ideal_span_isMaximal_of_prime p).isPrime
  ne_bot := Ideal.span_singleton_eq_bot.not.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

/-- Membership in the integer ideal-primary component is exactly membership
in the ordinary `p`-primary subgroup, with an element-dependent exponent. -/
theorem mem_integerPrime_iff (p : ℕ) [Fact p.Prime] (x : G) :
    x ∈ Ideal.primaryComponent G (integerPrime p).asIdeal ↔
      x ∈ primaryComponent G p := by
  rw [Ideal.primaryComponent_mem, mem_primaryComponent]
  simp only [integerPrime, Ideal.span_singleton_pow, Submodule.mem_torsionBySet_iff]
  constructor
  · rintro ⟨exponent, h⟩
    refine ⟨exponent, ?_⟩
    have hpow := h ⟨(p : ℤ) ^ exponent, Ideal.subset_span (Set.mem_singleton _)⟩
    simpa [← natCast_zsmul] using hpow
  · rintro ⟨exponent, hpow⟩
    refine ⟨exponent, ?_⟩
    rintro ⟨scalar, hscalar⟩
    obtain ⟨coefficient, hfactor⟩ := (Ideal.mem_span_singleton).1 hscalar
    have hint : ((p : ℤ) ^ exponent) • x = 0 := by
      simpa [← natCast_zsmul] using hpow
    change scalar • x = 0
    rw [hfactor, mul_comm, mul_smul, hint, smul_zero]

/-- The ideal-primary component at `(p)` and the ordinary `p`-primary subgroup
are the same additive subgroup of any abelian group. -/
theorem integerPrime_subgroup (p : ℕ) [Fact p.Prime] :
    (Ideal.primaryComponent G (integerPrime p).asIdeal).toAddSubgroup =
      primaryComponent G p := by
  ext x
  exact mem_integerPrime_iff p x

/-- A group homomorphism restricts to its ordinary `p`-primary subgroups. -/
def primaryComponent.map (p : ℕ) (f : G →+ H) :
    primaryComponent G p →+ primaryComponent H p :=
  (f.domRestrict (primaryComponent G p)).codRestrict (primaryComponent H p) (fun x => by
    obtain ⟨exponent, hpow⟩ := (mem_primaryComponent).1 x.property
    apply (mem_primaryComponent).2
    refine ⟨exponent, ?_⟩
    change p ^ exponent • f (x : G) = 0
    simpa only [map_nsmul, map_zero] using congrArg f hpow)

/-- The restricted map acts on underlying elements as the original homomorphism. -/
@[simp] theorem primaryComponent.map_apply (p : ℕ) (f : G →+ H)
    (x : primaryComponent G p) :
    ((primaryComponent.map p f x : primaryComponent H p) : H) = f (x : G) := rfl

/-- The ideal-primary restricted map agrees on underlying elements with the
ordinary-subgroup restricted map, under the membership identification. -/
theorem integerPrime_map_agrees (p : ℕ) [Fact p.Prime]
    (f : G →+ H) (x : primaryComponent G p) :
    ((Ideal.primaryComponent.map (integerPrime p).asIdeal f.toIntLinearMap)
      (⟨x, (mem_integerPrime_iff p (x : G)).2 x.property⟩ :
        Ideal.primaryComponent G (integerPrime p).asIdeal) : H) =
      (primaryComponent.map p f x : H) := rfl

/-- Exactness on the ordinary `p`-primary subgroups of abelian groups.
The source group must be torsion; the middle and target are arbitrary. -/
theorem primaryComponent.exact (hG : IsAddTorsion G) (p : ℕ) [Fact p.Prime]
    (f : G →+ H) (g : H →+ K) (hfg : Function.Exact f g) :
    Function.Exact (primaryComponent.map p f) (primaryComponent.map p g) := by
  have hIdeal := Ideal.primaryComponent.exact
    (isAddTorsion_iff_isTorsion_int.mp hG) (integerPrime p)
    f.toIntLinearMap g.toIntLinearMap hfg
  intro y
  constructor
  · intro hy
    have hgy := congrArg (fun z : primaryComponent K p => (z : K)) hy
    change g (y : H) = 0 at hgy
    let iy : Ideal.primaryComponent H (integerPrime p).asIdeal :=
      ⟨y, (mem_integerPrime_iff p (y : H)).2 y.property⟩
    have hiy : Ideal.primaryComponent.map (integerPrime p).asIdeal g.toIntLinearMap iy = 0 := by
      apply Subtype.ext
      exact hgy
    obtain ⟨ix, hix⟩ := (hIdeal iy).1 hiy
    refine ⟨⟨ix, (mem_integerPrime_iff p (ix : G)).1 ix.property⟩, Subtype.ext ?_⟩
    have heq := congrArg (fun z : Ideal.primaryComponent H (integerPrime p).asIdeal =>
      (z : H)) hix
    change f (ix : G) = (y : H) at heq
    exact heq
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    exact (hfg (f (x : G))).2 ⟨x, rfl⟩

end AddCommGroup

@[expose] public section

/-- A `p`-primary element is in the kernel of the integer-ideal restricted map exactly
when its underlying element is in the kernel of the original additive homomorphism.
The criterion uses the canonical integer action, with no torsion hypothesis on either group,
and the characteristic formulas `AddCommGroup.integerPrime_map_agrees` and
`AddCommGroup.primaryComponent.map_apply`. -/
theorem AddCommGroup.integerPrime_map_eq_zero_iff
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (p : ℕ) [Fact p.Prime] (f : G →+ H) (x : AddCommGroup.primaryComponent G p) :
    Ideal.primaryComponent.map (AddCommGroup.integerPrime p).asIdeal f.toIntLinearMap
        (⟨x, (AddCommGroup.mem_integerPrime_iff p (x : G)).2 x.property⟩ :
          Ideal.primaryComponent G (AddCommGroup.integerPrime p).asIdeal) = 0 ↔
      f (x : G) = 0 := by
  have hmap := AddCommGroup.integerPrime_map_agrees p f x
  rw [AddCommGroup.primaryComponent.map_apply] at hmap
  constructor
  · intro h
    have h' := congrArg
      (fun y : Ideal.primaryComponent H (AddCommGroup.integerPrime p).asIdeal ↦ (y : H)) h
    exact hmap.symm.trans h'
  · intro h
    apply Subtype.ext
    exact hmap.trans h

end
