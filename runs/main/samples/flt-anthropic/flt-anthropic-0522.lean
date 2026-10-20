namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_integers_ne_integers

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option linter.unusedSectionVars false

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

noncomputable section

open scoped Classical

p2m_open

namespace Ws25

namespace GaussE

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Dict

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)

local notation "kk" => IsLocalRing.ResidueField A

open ModularCurve.CharPReduction

theorem resHom_eq_modularRedLocHom {f : LaurentSeries L}
    (hO : f ∈ modularLocalized N A.toSubring (IsLocalRing.residue A)) (hF : f ∈ FF)
    (hG : (⟨f, hF⟩ : FF) ∈ gaussRing A N) :
    resHom A N ⟨⟨f, hF⟩, hG⟩
      = modularRedLocHom N A.toSubring (IsLocalRing.residue A) ⟨f, hO⟩ := by
  obtain ⟨r, s, hs, hfs⟩ := (mem_localizedAtKer _ _ _ _).mp hO
  obtain ⟨r₀, hr₀⟩ := exists_coeffMap_subtype_eq A (r : LaurentSeries L)
    (fun n => modularRing_le_integralCoeffs N A.toSubring r.2 n)
  obtain ⟨s₀, hs₀⟩ := exists_coeffMap_subtype_eq A (s : LaurentSeries L)
    (fun n => modularRing_le_integralCoeffs N A.toSubring s.2 n)
  have hϖs : ϖ A s₀ ≠ 0 := fun h0 => (notMem_redKer_iff _ _ _ _).mp hs
    (by rw [redRes_apply, coeffRed_eq_ϖ A _ s₀ hs₀.symm, h0])
  have hwit : (((⟨⟨f, hF⟩, hG⟩ : gaussRing A N) : FF) : LaurentSeries L) * ι A s₀ = ι A r₀ := by
    show f * ι A s₀ = ι A r₀
    rw [show ι A s₀ = s from hs₀, show ι A r₀ = r from hr₀]
    exact hfs
  rw [resHom_eq A N hϖs hwit]
  have hspec := redLoc_spec (A := A.toSubring) (red := IsLocalRing.residue A)
    (R := modularRing N A.toSubring) (hR := modularRing_le_integralCoeffs N A.toSubring)
    ⟨f, hO⟩ (r := r) (s := s) hfs
  rw [redRes_apply, redRes_apply, coeffRed_eq_ϖ A _ s₀ hs₀.symm,
    coeffRed_eq_ϖ A _ r₀ hr₀.symm] at hspec
  rw [show modularRedLocHom N A.toSubring (IsLocalRing.residue A) ⟨f, hO⟩ = redLoc ⟨f, hO⟩ from rfl,
    div_eq_iff hϖs]
  exact hspec.symm

end Dict
end GaussE
end Ws25
end
end P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_integers_ne_integers
