namespace P2MW.S_ModularCurve_kroneckerCongruence

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option autoImplicit false

noncomputable section

p2m_open

namespace ModularCurve p2m_export "ModularCurve" "ModularPolynomialData jqModC jqNModC map_jqModC jqInt jqIntN reduceModBivar KroneckerCongruence jqMod jqNMod modularPolynomial_kronecker" end ModularCurve

p2m_open_scoped "ModularCurve" in

p2m_open_scoped "ModularCurve" in

p2m_open_scoped "ModularCurve" in

p2m_open_scoped "ModularCurve" in

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.kroneckerCongruence_of_map_eq (ℓ : ℕ) [NeZero ℓ]
    (data : ModularPolynomialData ℓ)
    (h : data.Φ.map (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))) =
      (Polynomial.C Polynomial.X ^ ℓ - Polynomial.X) *
        (Polynomial.C Polynomial.X - Polynomial.X ^ ℓ)) :
    KroneckerCongruence ℓ data := by
  show reduceModBivar ℓ data.Φ = _
  rw [reduceModBivar]
  exact h

end ModularCurve
end
end P2MW.S_ModularCurve_kroneckerCongruence
