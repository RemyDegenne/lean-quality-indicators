public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.TauCetiBridge CFSG.Timmesfeld.ExceptionalOrders CFSG.LieType.Ree
  CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.SteinbergBT

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (fieldAut_isCyclic)

open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

set_option linter.unusedSectionVars false

theorem fieldCoreAt_entrywise_G2_two {f p : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp6048 : p ∣ 6048) {σ : K ≃+* K}
    (hσp : orderOf σ = p) (hk2 : Nat.card (fixSubfield σ) = 2) :
    FieldCoreAt p (entrywiseAdjointAut Tag.G2 σ) := by
  classical
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨-, -, hJC, hfixeq, -, -, -, -, -, -, hcent, -, -⟩ :=
    even_G2_canonical_field_centralizer_all_orders hf hK σ
  have : Finite (fixSubfield σ) := Subtype.finite
  have hmemφ : ∀ a : adjointGroup Tag.G2 (fixSubfield σ),
      baseChangeGL (fixSubfield σ).subtype (a : ModGL Tag.G2 (fixSubfield σ)) ∈
        adjointGroup Tag.G2 K := fun a => hJC ⟨a, a.2, rfl⟩
  obtain ⟨φ, hφdef⟩ : ∃ φ : adjointGroup Tag.G2 (fixSubfield σ) →* adjointGroup Tag.G2 K,
      ∀ a, (φ a : ModGL Tag.G2 K) =
        baseChangeGL (fixSubfield σ).subtype (a : ModGL Tag.G2 (fixSubfield σ)) :=
    ⟨((baseChangeGL (fixSubfield σ).subtype).comp
      (adjointGroup Tag.G2 (fixSubfield σ)).subtype).codRestrict _ hmemφ, fun _ => rfl⟩
  have hφ : Function.Injective φ := fun a b h =>
    Subtype.ext (baseChangeGL_injective _ (by rw [← hφdef, ← hφdef, h]))
  have hJfix : ∀ g : adjointGroup Tag.G2 K, g ∈ φ.range ↔ entrywiseAdjointAut Tag.G2 σ g = g := by
    intro g
    have h1 : g ∈ φ.range ↔ (g : ModGL Tag.G2 K) ∈ fixedFieldImage Tag.G2 σ := by
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a, a.2, (hφdef a).symm⟩
      · rintro ⟨a, ha, hga⟩
        exact ⟨⟨a, ha⟩, Subtype.ext ((hφdef _).trans hga)⟩
    rw [h1, ← hfixeq]
    constructor
    · rintro ⟨g', hg', hgg'⟩
      have : g' = g := Subtype.ext hgg'
      subst this
      exact hg'
    · intro h
      exact ⟨g, h, rfl⟩
  obtain ⟨hq, hTcard, hZT, hJcard, hZJ⟩ := derived_range_adjointG2_two (fixSubfield σ) hk2 φ hφ
  obtain ⟨hTJ, hTn⟩ := commutator_self_le_and_normalized φ.range
  have hidx : (⁅φ.range, φ.range⁆.subgroupOf φ.range).index = 2 := by
    have h := (⁅φ.range, φ.range⁆.subgroupOf φ.range).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJ).toEquiv, hTcard, hJcard] at h
    omega
  refine ⟨⁅φ.range, φ.range⁆, fun t ht => (hJfix t).1 (hTJ ht),
    fun f hf t ht => hTn f ((hJfix f).2 hf) t ht, hq, ?_, ?_⟩
  · rw [hTcard, Nat.Prime.coprime_iff_not_dvd hp]
    exact not_not.2 hp6048
  · intro g hgp hgδ hgT
    have hgJ : ∀ j ∈ φ.range, g j ∈ φ.range := by
      intro j hj
      rw [hJfix]
      have h1 := congrArg (fun β : MulAut (adjointGroup Tag.G2 K) => β j) hgδ
      simp only [MulAut.mul_apply] at h1
      rw [← h1, (hJfix j).1 hj]
    have hfixJ := fixes_of_fixes_derived φ.range hidx hZT hZJ g hgJ hgT
    have hJ₀ : φ.range = (fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K) := by
      ext j
      rw [Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a, a.2, (hφdef a).symm⟩
      · rintro ⟨a, ha, hga⟩
        exact ⟨⟨a, ha⟩, Subtype.ext ((hφdef _).trans hga)⟩
    have hg1 : g ∈ Subgroup.centralizer {entrywiseAdjointAut Tag.G2 σ} ⊓
        Subgroup.centralizer ((((fixedFieldImage Tag.G2 σ).subgroupOf
          (adjointGroup Tag.G2 K)).map MulAut.conj : Subgroup (MulAut (adjointGroup Tag.G2 K))) :
            Set (MulAut (adjointGroup Tag.G2 K))) := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hgδ, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨j, hj, rfl⟩
      rw [← hJ₀] at hj
      have h1 := mul_conj_mul_inv g j
      rw [hfixJ j hj] at h1
      change MulAut.conj j * g = g * MulAut.conj j
      calc MulAut.conj j * g = (g * MulAut.conj j * g⁻¹) * g := by rw [h1]
        _ = g * MulAut.conj j := by group
    rw [hcent] at hg1
    have hδp : orderOf (entrywiseAdjointAut Tag.G2 σ) = p :=
      (orderOf_entrywiseAdjointAut (by decide : 0 < Tag.G2.rank) σ).trans hσp
    have hdvd : orderOf g ∣ p := hδp ▸ orderOf_dvd_of_mem_zpowers hg1
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hgp.symm hdvd)

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
end
