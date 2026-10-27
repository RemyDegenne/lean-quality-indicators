public noncomputable section

namespace CFSG.StandardType.TwE6FixedA2Type

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.Three
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6NonToralThree
  CFSG.StandardType.E6ThreeEnd CFSG.StandardType.TwE6HyperplaneTypes
  CFSG.LieType.Steinberg.Adjoint

local instance tableBE6FixA2NeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section FixedType

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Lang.E6Descent CFSG.ComponentClassification.CatalogueBPrimeJoin
  CFSG.HardMathSupport.Timmesfeld.Torality

variable
  {Ω : Type} [Field Ω]

theorem isQuasisimple_jgeom_or_centralizes_fixedA2 {Fr : Ω →+* Ω}
    {Hh : Subgroup (ModGL Tag.E6 Ω)}
    [Finite ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)]
    {n : ℕ} (hn : 3 ≤ n) {k : Type} [Field k] [Finite k] [Algebra k Ω] [IsAlgClosure k Ω]
    (hk : Nat.card k = (2 ^ n) ^ 2) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (hHF : Hh ≤ TwistedDiag.Rgrp Ω Fr)
    {y₀ : ModGL Tag.E6 Ω} (hy₀ : y₀ ∈ adjointGroup Tag.E6 Ω) {x : ModGL Tag.E6 Ω}
    (hxM : x ∈ monomialSubgroup Tag.E6 Ω) (hxc : weylQuotientHom Tag.E6 Ω ⟨x, hxM⟩ = cE6)
    {ζ : Ωˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    (hHgen : Hh.map (MulAut.conj y₀).toMonoidHom = Subgroup.closure
      ((fun v => rootDiagUnit Tag.E6 (zetaVec ζ hζ v)) ''
        {v | ∃ x', x' 0 = 0 ∧ v = combC x'} ∪ {x}))
    {e g : ModGL Tag.E6 Ω}
    (heK : e ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (heF : e ∈ TwistedDiag.Rgrp Ω Fr) (he1 : e ≠ 1) (he3 : e ^ 3 = 1)
    (hgK : g ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hgF : g ∈ TwistedDiag.Rgrp Ω Fr) {t : ℕ} (hg2 : g ^ (2 ^ t) = 1)
    (hinv : g * e * g⁻¹ = e⁻¹) {be : Fin Tag.E6.rank → Ωˣ}
    (heT : y₀ * e * y₀⁻¹ = rootDiagUnit Tag.E6 be) :
    CFSG.IsQuasisimple ((primeResidual 2 ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)).map
        (closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr).subtype) ∨
    rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6} ≤ Subgroup.centralizer {x} := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * n)
    (by rw [← Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm])
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  set H' := Hh.map (MulAut.conj y₀).toMonoidHom with hH'
  set K' := closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
    Subgroup.centralizer (H' : Set (ModGL Tag.E6 Ω))) with hK'def
  set Hs : Set (Fin Tag.E6.rank → ZMod 3) := {v | ∃ x', x' 0 = 0 ∧ v = combC x'} with hHs
  have ha : ∀ v ∈ Hs, rootDiagUnit Tag.E6 (zetaVec ζ hζ v) ∈ H' := fun v hv => by
    rw [hHgen]
    exact Subgroup.subset_closure (Set.mem_union_left _ ⟨v, hv, rfl⟩)
  have hxH : x ∈ H' := by
    rw [hHgen]
    exact Subgroup.subset_closure (Set.mem_union_right _ rfl)
  have hSig : ∀ α, (IsRoot .E6 α ∧ ∀ v ∈ Hs, rootChar (zetaVec ζ hζ v) α = 1) ↔
      α ∈ fixedA2E6 := isRoot_and_rootChar_zetaVec_iff hζo hζ
  have hKS : ∀ z ∈ K', z ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6} :=
    fun z hz => mem_torus_sup_fixedA2_of_mem_closedIdentityComponent hζo hζ ha hz
  have hmaps := mapsRootLines_weylQuotientHom (R := Ω) ⟨x, hxM⟩
  have hfix : ∀ γ ∈ fixedA2E6, weylQuotientHom Tag.E6 Ω ⟨x, hxM⟩ • γ = γ := fun γ hγ => by
    rw [hxc, cE6_smul]
    exact cAct_fixedA2E6 γ hγ
  have hm1 : gamma1 ∈ fixedA2E6 := mem_fixedA2E6.2 (Or.inl rfl)
  have hm2 : gamma2 ∈ fixedA2E6 := mem_fixedA2E6.2 (Or.inr (Or.inl rfl))
  have hm3 : gamma3 ∈ fixedA2E6 := mem_fixedA2E6.2 (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨s₁, hs₁⟩ := CFSG.RankThree.Chevalley.exists_conj_rootSL2_eq hxM hmaps isRoot_gamma1
    (hfix gamma1 hm1)
  obtain ⟨s₂, hs₂⟩ := CFSG.RankThree.Chevalley.exists_conj_rootSL2_eq hxM hmaps isRoot_gamma2
    (hfix gamma2 hm2)
  obtain ⟨s₃, hs₃⟩ := CFSG.RankThree.Chevalley.exists_conj_rootSL2_eq hxM hmaps isRoot_gamma3
    (hfix gamma3 hm3)
  have hs₁₂ : s₃ = s₁ * s₂ := twist_mul_of_conj hs₁ hs₂ hs₃
  have hcx : ∀ γ, (∀ A, x * rootSL2 .E6 Ω γ A * x⁻¹ = rootSL2 .E6 Ω γ
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne 1) A)) →
      ∀ A, x * rootSL2 .E6 Ω γ A = rootSL2 .E6 Ω γ A * x := by
    intro γ h A
    have h' := h A
    rw [CFSG.RankThree.Chevalley.diagUnitOne_one, CFSG.RankThree.Classical.conjSL_one] at h'
    calc x * rootSL2 .E6 Ω γ A = (x * rootSL2 .E6 Ω γ A * x⁻¹) * x := by group
      _ = rootSL2 .E6 Ω γ A * x := by rw [h']
  by_cases hs : s₁ = 1 ∧ s₂ = 1
  ·
    right
    obtain ⟨rfl, rfl⟩ := hs
    rw [one_mul] at hs₁₂
    subst hs₁₂
    exact rootSpan_fixedA2_le_centralizer (hcx _ hs₁) (hcx _ hs₂) (hcx _ hs₃)
  left
  set bτ : Fin Tag.E6.rank → Ωˣ := ![1, s₂ * s₁⁻¹, 1, s₁, 1, 1] with hbτ
  have hb1 : rootChar bτ gamma1 = s₁ := by
    change ∏ i : Fin 6, bτ i ^ gamma1 i = s₁
    simp [hbτ, gamma1, Fin.prod_univ_succ]
  have hb2 : rootChar bτ gamma2 = s₂ := by
    change ∏ i : Fin 6, bτ i ^ gamma2 i = s₂
    simp [hbτ, gamma2, Fin.prod_univ_succ]
  have hb3 : rootChar bτ gamma3 = s₃ := by
    rw [gamma3_eq, rootChar_add, hb1, hb2, hs₁₂]
  have hx'c : ∀ γ, IsRoot .E6 γ → ∀ s : Ωˣ, rootChar bτ γ = s →
      (∀ A, x * rootSL2 .E6 Ω γ A * x⁻¹ = rootSL2 .E6 Ω γ
        (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s) A)) →
      ∀ A, (rootDiagUnit Tag.E6 bτ)⁻¹ * x * rootSL2 .E6 Ω γ A =
        rootSL2 .E6 Ω γ A * ((rootDiagUnit Tag.E6 bτ)⁻¹ * x) := by
    intro γ hγ s hbs hxs A
    have h2 := CFSG.RankThree.Chevalley.rootDiagUnit_conj_rootSL2 bτ hγ A
    rw [hbs] at h2
    calc (rootDiagUnit Tag.E6 bτ)⁻¹ * x * rootSL2 .E6 Ω γ A =
        (rootDiagUnit Tag.E6 bτ)⁻¹ * (x * rootSL2 .E6 Ω γ A * x⁻¹) * rootDiagUnit Tag.E6 bτ *
          ((rootDiagUnit Tag.E6 bτ)⁻¹ * x) := by group
      _ = (rootDiagUnit Tag.E6 bτ)⁻¹ *
          (rootDiagUnit Tag.E6 bτ * rootSL2 .E6 Ω γ A * (rootDiagUnit Tag.E6 bτ)⁻¹) *
            rootDiagUnit Tag.E6 bτ * ((rootDiagUnit Tag.E6 bτ)⁻¹ * x) := by rw [hxs A, h2]
      _ = rootSL2 .E6 Ω γ A * ((rootDiagUnit Tag.E6 bτ)⁻¹ * x) := by group
  have hUx' : rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6} ≤
      Subgroup.centralizer {(rootDiagUnit Tag.E6 bτ)⁻¹ * x} :=
    rootSpan_fixedA2_le_centralizer (hx'c _ isRoot_gamma1 s₁ hb1 hs₁)
      (hx'c _ isRoot_gamma2 s₂ hb2 hs₂) (hx'c _ isRoot_gamma3 s₃ hb3 hs₃)
  have hKτ : K' ≤ Subgroup.centralizer ({rootDiagUnit Tag.E6 bτ} : Set (ModGL Tag.E6 Ω)) :=
    fun z hz => Subgroup.mem_centralizer_singleton_iff.2
      (commute_twist_of_mem_closedIdentityComponent hxM hxc hxH hKS hUx' hz)
  set H'' := Subgroup.closure ((H' : Set (ModGL Tag.E6 Ω)) ∪ {rootDiagUnit Tag.E6 bτ}) with hH''
  have hC'' : adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer (H'' : Set (ModGL Tag.E6 Ω)) =
      (adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer (H' : Set (ModGL Tag.E6 Ω))) ⊓
        Subgroup.centralizer ({rootDiagUnit Tag.E6 bτ} : Set (ModGL Tag.E6 Ω)) := by
    rw [hH'', Subgroup.centralizer_closure, inf_assoc]
    congr 1
    ext z
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_union,
      Set.mem_singleton_iff, or_imp, forall_and, forall_eq, SetLike.mem_coe]
  have hK'' : closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (H'' : Set (ModGL Tag.E6 Ω))) = K' := by
    rw [hC'', closedIdentityComponent_inf_eq_of_le _ _ hKτ]
  let a'' : Option Hs → Fin Tag.E6.rank → Ωˣ := fun o =>
    Option.elim o bτ fun v => zetaVec ζ hζ (v : Fin Tag.E6.rank → ZMod 3)
  have ha'' : ∀ o, rootDiagUnit Tag.E6 (a'' o) ∈ H'' := by
    rintro (_ | v)
    · exact Subgroup.subset_closure (Set.mem_union_right _ rfl)
    · exact Subgroup.subset_closure (Set.mem_union_left _ (ha v.1 v.2))
  have hfam'' : ∀ z ∈ K', z ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (familyKernel a'') := by
    intro z hz
    rw [← hK''] at hz
    exact (closedIdentityComponent_le_familyGroup_inf_centralizer a'' ha'' hz).1
  have hFK : ∀ α ∈ familyKernel a'', α ∈ fixedA2E6 ∧ rootChar bτ α = 1 := by
    rintro α ⟨hα, hall⟩
    exact ⟨(hSig α).1 ⟨hα, fun v hv => hall (some ⟨v, hv⟩)⟩, hall none⟩
  have hrank1 : ∀ γ, IsRoot .E6 γ → γ ∈ fixedA2E6 →
      (∃ ℓ ∈ rootFinset .E6, ∑ i, ℓ i * corootPair γ (Pi.single i 1) = 1) →
      (∀ A, x * rootSL2 .E6 Ω γ A * x⁻¹ = rootSL2 .E6 Ω γ
        (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne 1) A)) →
      (∀ α ∈ familyKernel a'', α = γ ∨ α = -γ) →
      CFSG.IsQuasisimple ((primeResidual 2 ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
        Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)).map
          (closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
            Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓
              TwistedDiag.Rgrp Ω Fr).subtype) := by
    rintro γ hγ hγS ⟨ℓ, hℓ, hℓ1⟩ hxγ hsub
    have hγH : ∀ h ∈ H', ∀ A, h * rootSL2 .E6 Ω γ A = rootSL2 .E6 Ω γ A * h := by
      intro h hh A
      rw [hHgen] at hh
      induction hh using Subgroup.closure_induction with
      | mem y hy =>
        rcases hy with ⟨v, hv, rfl⟩ | hy
        · have hc := CFSG.RankThree.Chevalley.rootDiagUnit_conj_rootSL2 (zetaVec ζ hζ v) hγ A
          rw [((hSig γ).2 hγS).2 v hv, CFSG.RankThree.Chevalley.diagUnitOne_one,
            CFSG.RankThree.Classical.conjSL_one] at hc
          calc rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * rootSL2 .E6 Ω γ A =
              (rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * rootSL2 .E6 Ω γ A *
                (rootDiagUnit Tag.E6 (zetaVec ζ hζ v))⁻¹) * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) := by
                group
            _ = rootSL2 .E6 Ω γ A * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) := by rw [hc]
        · rw [Set.mem_singleton_iff.1 hy]
          exact hcx γ hxγ A
      | one => rw [one_mul, mul_one]
      | mul y z _ _ hy hz => rw [mul_assoc, hz, ← mul_assoc, hy, mul_assoc]
      | inv y _ hy => exact (Commute.inv_left (hy : Commute y (rootSL2 .E6 Ω γ A))).eq
    have hmono : rootSpan Tag.E6 Ω (familyKernel a'') ≤ rootSpan Tag.E6 Ω {γ, -γ} :=
      biSup_mono fun α hα => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact hsub α hα
    exact isQuasisimple_jgeom_of_rootPair hn hk hFr hHF hy₀ hγ
      (ℓ₁ := Sum.inr ⟨ℓ, mem_rootFinset.mp hℓ⟩) hℓ1 hγH
      (fun z hz => sup_le_sup_left hmono _ (hfam'' z hz)) heK heF he1 he3 hgK hgF hg2 hinv heT
  have hneg : ∀ γ, rootChar bτ (-γ) = 1 → rootChar bτ γ = 1 := fun γ h => by
    rwa [CFSG.RankThree.Chevalley.rootChar_neg', inv_eq_one] at h
  by_cases h1 : s₁ = 1
  ·
    have h2 : s₂ ≠ 1 := fun h2 => hs ⟨h1, h2⟩
    refine hrank1 gamma1 isRoot_gamma1 hm1 exists_corootPair_gamma1 (h1 ▸ hs₁) fun α hα => ?_
    obtain ⟨hαS, hαb⟩ := hFK α hα
    rcases mem_fixedA2E6.1 hαS with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd (hb2 ▸ hαb) h2
    · exact absurd (by rw [hb3, hs₁₂, h1, one_mul] at hαb; exact hαb) h2
    · exact Or.inr rfl
    · exact absurd (hb2 ▸ hneg _ hαb) h2
    · exact absurd (by have h' := hneg _ hαb; rw [hb3, hs₁₂, h1, one_mul] at h'; exact h') h2
  by_cases h2 : s₂ = 1
  ·
    refine hrank1 gamma2 isRoot_gamma2 hm2 exists_corootPair_gamma2 (h2 ▸ hs₂) fun α hα => ?_
    obtain ⟨hαS, hαb⟩ := hFK α hα
    rcases mem_fixedA2E6.1 hαS with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (hb1 ▸ hαb) h1
    · exact Or.inl rfl
    · exact absurd (by rw [hb3, hs₁₂, h2, mul_one] at hαb; exact hαb) h1
    · exact absurd (hb1 ▸ hneg _ hαb) h1
    · exact Or.inr rfl
    · exact absurd (by have h' := hneg _ hαb; rw [hb3, hs₁₂, h2, mul_one] at h'; exact h') h1
  by_cases h3 : s₁ * s₂ = 1
  ·
    refine hrank1 gamma3 isRoot_gamma3 hm3 exists_corootPair_gamma3 ((hs₁₂.trans h3) ▸ hs₃)
      fun α hα => ?_
    obtain ⟨hαS, hαb⟩ := hFK α hα
    rcases mem_fixedA2E6.1 hαS with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (hb1 ▸ hαb) h1
    · exact absurd (hb2 ▸ hαb) h2
    · exact Or.inl rfl
    · exact absurd (hb1 ▸ hneg _ hαb) h1
    · exact absurd (hb2 ▸ hneg _ hαb) h2
    · exact Or.inr rfl
  exfalso
  have hFKe : familyKernel a'' = ∅ := by
    ext α
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hα
    obtain ⟨hαS, hαb⟩ := hFK α hα
    rcases mem_fixedA2E6.1 hαS with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1 (hb1 ▸ hαb)
    · exact h2 (hb2 ▸ hαb)
    · exact h3 (by rw [hb3, hs₁₂] at hαb; exact hαb)
    · exact h1 (hb1 ▸ hneg _ hαb)
    · exact h2 (hb2 ▸ hneg _ hαb)
    · exact h3 (by have h' := hneg _ hαb; rw [hb3, hs₁₂] at h'; exact h')
  have hbot : rootSpan Tag.E6 Ω (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ := by
    simp only [rootSpan, Set.mem_empty_iff_false, iSup_false, iSup_bot]
  have hKT : ∀ z ∈ K', z ∈ torusGroup Tag.E6 Ω := by
    intro z hz
    have h := hfam'' z hz
    rwa [hFKe, hbot, sup_bot_eq] at h
  have hgT := hKT _ ((TwE6FixedComponent.conj_mem_closedIdentityComponent_iff hy₀ g).2 hgK)
  have heT' := hKT _ ((TwE6FixedComponent.conj_mem_closedIdentityComponent_iff hy₀ e).2 heK)
  obtain ⟨bg, hbg⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgT
  obtain ⟨be', hbe⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup heT'
  have hcomm : (y₀ * g * y₀⁻¹) * (y₀ * e * y₀⁻¹) = (y₀ * e * y₀⁻¹) * (y₀ * g * y₀⁻¹) := by
    rw [hbg, hbe, ← CFSG.LieType.Chevalley.rootDiagUnit_mul,
      ← CFSG.LieType.Chevalley.rootDiagUnit_mul, mul_comm]
  have hge : g * e = e * g := by
    have h := congrArg (fun v => y₀⁻¹ * v * y₀) hcomm
    rw [show y₀⁻¹ * (y₀ * g * y₀⁻¹ * (y₀ * e * y₀⁻¹)) * y₀ = g * e by group,
      show y₀⁻¹ * (y₀ * e * y₀⁻¹ * (y₀ * g * y₀⁻¹)) * y₀ = e * g by group] at h
    exact h
  have hee : e = e⁻¹ := by rw [← hinv, hge, mul_inv_cancel_right]
  apply he1
  have h2e : e ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [hee]
    exact mul_inv_cancel e
  calc e = e ^ 3 * (e ^ 2)⁻¹ := by group
    _ = 1 := by rw [he3, h2e]; group

end FixedType
end CFSG.StandardType.TwE6FixedA2Type
end
