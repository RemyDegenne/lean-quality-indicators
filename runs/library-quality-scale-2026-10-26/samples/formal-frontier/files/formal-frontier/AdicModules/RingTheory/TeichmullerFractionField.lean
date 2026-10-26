/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.RingTheory.Teichmuller
public import AdicModules.RingTheory.Perfection
public import Mathlib.RingTheory.Valuation.Integral

/-!
# Teichmüller images in fraction fields

For a valuation domain complete along a maximal ideal `I`, the image
characterization uses the existing `Perfection.teichmuller₀ p I` followed by the
specified fraction-field algebra map. The residue field is the quotient
`R ⧸ I`; it need not be perfect or finite. No topology on the fraction field is
part of the hypotheses.

The characterization laws concern independently existing roots at every depth,
including zero and `n = 0`, rather than a supplied compatible root family. Integral
closedness brings roots of ring elements back to the valuation ring; inversion
in the perfection of the residue field handles the remaining fraction elements.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second
  edition, I §7, (7.1), for the fraction-field perfect-core image characterization.
* Kenny Lau's Mathlib Teichmüller construction, and the adic-ring image laws in
  `AdicModules.RingTheory.Teichmuller`.

This module gives only the fraction-field extension of the image law, not all
of (7.1), Corollary 1 of (7.3), or (7.2).
-/

@[expose] public section

universe u v

namespace Perfection

variable (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [IsDomain R]
    [hval : ValuationRing R] (I : Ideal R) [hmax : I.IsMaximal] [IsAdicComplete I R]
    [CharP (R ⧸ I) p] (K : Type v) [Field K] [Algebra R K] [hfrac : IsFractionRing R K]

include hval hmax hfrac

/-- Membership in the fraction-field Teichmüller image is equivalent to the
existence of separate `p^n`-th roots at each depth, including zero and `n = 0`.
This extends the image characterization of Fesenko–Vostokov, I §7, (7.1). -/
theorem mem_range_algebraMap_comp_teichmuller₀_iff (x : K) :
    x ∈ Set.range ((algebraMap R K).toMonoidWithZeroHom.comp (teichmuller₀ p I)) ↔
      ∀ n : ℕ, ∃ y : K, y ^ (p ^ n) = x := by
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  let : IsIntegrallyClosed R := (ValuationRing.integers R K).isIntegrallyClosed
  constructor
  · rintro ⟨a, rfl⟩ n
    obtain ⟨r, hr⟩ := (mem_range_teichmuller₀_iff p I (teichmuller₀ p I a)).mp ⟨a, rfl⟩ n
    refine ⟨algebraMap R K r, ?_⟩
    change algebraMap R K r ^ (p ^ n) = algebraMap R K (teichmuller₀ p I a)
    rw [← map_pow, hr]
  · intro hx
    -- Roots of an integer are integral, hence lie in the integrally closed valuation ring.
    have lift_integer (z : K) (hz : IsLocalization.IsInteger R z)
        (hroots : ∀ n : ℕ, ∃ y : K, y ^ (p ^ n) = z) :
        z ∈ Set.range ((algebraMap R K).toMonoidWithZeroHom.comp (teichmuller₀ p I)) := by
      obtain ⟨r, rfl⟩ := hz
      have hr : ∀ n : ℕ, ∃ s : R, s ^ (p ^ n) = r := by
        intro n
        obtain ⟨y, hy⟩ := hroots n
        have hyi : IsIntegral R (y ^ (p ^ n)) := by
          rw [hy]
          exact isIntegral_algebraMap
        obtain ⟨s, hs⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
          (pow_pos (Fact.out : p.Prime).pos n) hyi
        refine ⟨s, IsFractionRing.injective R K ?_⟩
        rw [map_pow, hs, hy]
      obtain ⟨a, ha⟩ := (mem_range_teichmuller₀_iff p I r).mpr hr
      exact ⟨a, congrArg (algebraMap R K) ha⟩
    rcases ValuationRing.isInteger_or_isInteger R x with hxR | hxR
    · exact lift_integer x hxR hx
    · have hinv : ∀ n : ℕ, ∃ y : K, y ^ (p ^ n) = x⁻¹ := by
        intro n
        obtain ⟨y, hy⟩ := hx n
        exact ⟨y⁻¹, by rw [inv_pow, hy]⟩
      obtain ⟨a, ha⟩ := lift_integer x⁻¹ hxR hinv
      -- Invert in the canonical perfection field, keeping the same composite map.
      refine ⟨a⁻¹, ?_⟩
      rw [map_inv₀, ha, inv_inv]

/-- The Teichmüller image in the specified fraction field is the intersection
of all `p^n`-power images. No compatible family of roots is assumed.
This extends the image characterization of Fesenko–Vostokov, I §7, (7.1). -/
theorem range_algebraMap_comp_teichmuller₀ :
    Set.range ((algebraMap R K).toMonoidWithZeroHom.comp (teichmuller₀ p I)) =
      ⋂ n : ℕ, Set.range (fun y : K ↦ y ^ (p ^ n)) := by
  ext x
  rw [mem_range_algebraMap_comp_teichmuller₀_iff p I K]
  simp only [Set.mem_iInter, Set.mem_range]

end Perfection
