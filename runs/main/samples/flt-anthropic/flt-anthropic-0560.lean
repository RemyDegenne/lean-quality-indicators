namespace P2MW.S_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

p2m_open

namespace AlgebraicCurve

p2m_open

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

p2m_open

variable (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

namespace CanonicalLocalResidueDataK p2m_export "AlgebraicCurve.Place.CanonicalLocalResidueDataK" "res_higherPoleMonomial res_algebraMap_mul_uniformizer_pow_inv" end CanonicalLocalResidueDataK

p2m_open_scoped "AlgebraicCurve.Place.CanonicalLocalResidueDataK" in

theorem CanonicalLocalResidueDataK.res_differentialCoeff_D_of_mem_poleSubmodule
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) (N : ℕ) {g : F} (hg : g ∈ v.poleSubmodule N) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F g)) = 0 := by
  induction N generalizing g with
  | zero =>

    have hg' : g ∈ v.toValuationSubring := by
      have h := (v.mem_poleSubmodule (n := 0) (f := g)).mp hg
      rwa [pow_zero, one_mul] at h
    exact R.res_of_mem _ (hint g hg')
  | succ N ih =>

    obtain ⟨c, hc⟩ := hsurj (v.laurentTailCoeff (N + 1) ⟨g, hg⟩)
    have hclift : IsLocalRing.residue _ (algebraMap K v.toValuationSubring c)
        = v.laurentTailCoeff (N + 1) ⟨g, hg⟩ := by
      rw [← hc, IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
    have hrem : g - algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹ ∈ v.poleSubmodule N := by
      have h := v.laurentTail_remainder_mem_poleSubmodule hg hclift
      rwa [v.coe_algebraMap] at h

    have hpeel : R.res (v.differentialCoeff (KaehlerDifferential.D K F
        (algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹))) = 0 := by
      rw [Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero,
        v.differentialCoeff_smul, v.differentialCoeff_D_uniformizer_pow_inv,
        show algebraMap K F c * (-((N + 1 : ℕ) : F) * (v.uniformizer ^ (N + 2))⁻¹)
            = algebraMap K F (c * -((N + 1 : ℕ) : K)) * (v.uniformizer ^ ((N + 1) + 1))⁻¹ by
          rw [map_mul, _root_.map_neg, map_natCast]; ring]
      exact R.res_algebraMap_mul_uniformizer_pow_inv v (Nat.le_add_left 1 N) _

    have hsplit : R.res (v.differentialCoeff (KaehlerDifferential.D K F g))
        = R.res (v.differentialCoeff (KaehlerDifferential.D K F
            (g - algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹)))
          + R.res (v.differentialCoeff (KaehlerDifferential.D K F
            (algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹))) := by
      conv_lhs => rw [show g = (g - algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹)
          + algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹ by ring]
      rw [map_add, v.differentialCoeff_add'', map_add]
    rw [hsplit, ih hrem, hpeel, add_zero]

end CanonicalLocalResidueDataK
end Place
end AlgebraicCurve
end
end P2MW.S_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap
