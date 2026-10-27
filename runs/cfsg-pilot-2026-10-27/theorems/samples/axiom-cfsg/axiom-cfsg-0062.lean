public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Sporadic.Schreier.Tits TauCeti

set_option linter.unusedSectionVars false

section Ree

theorem exists_fixSubgroup_fieldAut_equiv {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    ∃ (b : ℕ) (_ : Nat.card (fixSubfield σ) = 2 ^ (2 * b + 1))
      (_ : CharP (fixSubfield σ) ReeTag.F4.prime),
      Nonempty (↥(fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) ≃*
        ↥(ReeTag.F4.reeGamma (fixSubfield σ) b)) := by
  classical
  obtain ⟨b, -, hkcard, hfixed⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.largeRee_fixed_data_odd hK hp hp2 σ hσ
  have : Finite (fixSubfield σ) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP (fixSubfield σ) ReeTag.F4.prime := by
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := 2 * b + 1) (by
      rw [← Nat.card_eq_fintype_card, hkcard]
      rfl)
  haveI := hchar
  have hFix : fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) =
      (ReeTag.F4.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _) := rfl
  refine ⟨b, hkcard, hchar, ⟨?_⟩⟩
  exact (((fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)).equivMapOfInjective
      (ReeTag.F4.reeGamma K a).subtype (ReeTag.F4.reeGamma K a).subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [hFix]; exact hfixed))).trans
    ((ReeTag.F4.reeGamma (fixSubfield σ) b).equivMapOfInjective _
      (baseChangeGL_injective (τ := ReeTag.F4.tag) (fixSubfield σ).subtype)).symm

end Ree
end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
end
