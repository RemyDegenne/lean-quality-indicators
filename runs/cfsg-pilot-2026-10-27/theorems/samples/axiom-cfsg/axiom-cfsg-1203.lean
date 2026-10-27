public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical CFSG.RankThree.QuadraticSL2 TrialitySplitInner TrialityFold
  SteinbergBT.TrialityPlane

open Subgroup

open scoped Pointwise commutatorElement

theorem triality_thetaT_eq_bot_qplus
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ ℓ ^ f + 1)
    (B : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hB : (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ≤ B)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) :
    thetaT p E = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨⟨Θ, hΘ, -⟩, -, hZ⟩ := triality_fieldQuotient_data hℓ hf K hK σ hσ
  have hinj : Function.Injective (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    mulAut_conj_injective_of_center_eq_bot hZ
  have hEpow : ∀ a ∈ E, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) a ha
  by_cases hEinn : E.map B.subtype ≤
    (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range
  swap
  ·
    obtain ⟨b, hbE, hbinn⟩ : ∃ b ∈ E,
        (b : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∉
          (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
            MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
      by_contra h
      push Not at h
      exact hEinn (by rintro _ ⟨b, hb, rfl⟩; exact h b hb)
    have hb1 : b ≠ 1 := fun h => hbinn (by rw [h]; exact one_mem _)
    have hbp : orderOf b = p := orderOf_eq_prime (hEpow b hbE) hb1
    have hcore := (triality_noninner_large_prime_field_descent_and_local_core_trivial hℓ hf K hK
      σ hσ Θ hΘ hp hp3 B hB b hbinn hbp).2.2.2
    refine eq_bot_iff.2 (iInf_le_of_le b (iInf_le_of_le hbE (iInf_le_of_le hb1 ?_)))
    rw [inSubgroup, hcore, Subgroup.map_bot]
  set Pl : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (E.map B.subtype).comap MulAut.conj with hPl
  have hPmap : Pl.map MulAut.conj = E.map B.subtype := Subgroup.map_comap_eq_self hEinn
  have eP : E ≃* Pl := (Subgroup.equivMapOfInjective E B.subtype B.subtype_injective).trans
    ((MulEquiv.subgroupCongr hPmap.symm).trans (Subgroup.equivMapOfInjective Pl _ hinj).symm)
  have hPcard : Nat.card Pl = p ^ 2 := by rw [← Nat.card_congr eP.toEquiv, hEcard]
  have hPp : IsPGroup p Pl := (IsElementaryAbelian.isPGroup p E).of_equiv eP
  have hPpow : ∀ c ∈ Pl, c ^ p = 1 := fun c hc => by
    obtain ⟨e, he, hee⟩ := hc
    apply hinj
    rw [map_pow, ← hee, map_one]
    exact congrArg Subtype.val (hEpow e he)
  have hPE : ∀ c ∈ Pl, (⟨MulAut.conj c, hB ⟨c, rfl⟩⟩ : B) ∈ E := fun c hc => by
    obtain ⟨e, he, hee⟩ := hc
    rwa [show (⟨MulAut.conj c, hB ⟨c, rfl⟩⟩ : B) = e from Subtype.ext hee.symm]
  obtain ⟨K₂, _, _, σ₂, τ, g, hK₂, hσ₂, hτ, hg, hzg⟩ := exists_qplus_setting hℓ hf hK σ hσ
  have : Finite K₂ := Nat.finite_of_card_ne_zero (by
    rw [hK₂]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K₂ ℓ := finite_field_prime_power_characteristic hℓ (k := f * 6) (by omega)
    (by rw [hK₂, pow_mul])
  have : Finite (ModGL TwistTag.D4.tag K₂) := finite_modGL
  obtain ⟨-, -, -, hall⟩ := triality_qplus_quadratic_realization_and_toral_Sylow ℓ f hℓ hf K K₂
    hK hK₂ σ.toRingHom hσ σ₂ hσ₂ τ.toRingHom hτ
  obtain ⟨-, hΓ, -⟩ := hall g hg hzg
  have hΓC : trialityConjImage K σ.toRingHom g ≤
      graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom := by
    rw [hΓ]
    exact inf_le_left
  obtain ⟨u, hu, hrange, hPT⟩ := exists_realization_le_torus hℓ hf hK hK₂ hσ hσ₂ hτ hg hzg hp hp3
    hpq hPp
  obtain ⟨F, hFdef⟩ : ∃ F, F = trialityRealization (σ := σ) (u * g) := ⟨_, rfl⟩
  rw [← hFdef] at hrange hPT
  have hF : Function.Injective F := by
    rw [hFdef]
    exact trialityRealization_injective _
  have hFΓ : ∀ c, F c ∈ trialityConjImage K σ.toRingHom g := fun c => by
    rw [← hrange]
    exact ⟨c, rfl⟩
  have hσ₂3 := sigma₂_pow_three hℓ hK₂ hσ₂
  obtain ⟨-, -, -, hL1, -⟩ := triality_all_characteristic_faithful_torus_coordinates K₂ σ₂ hσ₂3
  obtain ⟨V, hV⟩ : ∃ V : Subgroup (ModGL TwistTag.D4.tag K₂), ∀ x, x ∈ V ↔
      x ∈ graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ∧ x ^ p = 1 :=
    ⟨{ carrier := {x | x ∈ graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ∧ x ^ p = 1}
       mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
         rw [Commute.mul_pow (commute_of_mem_torusGroup
           (graphFixedRootTorus_le_torusGroup _ hx.1) (graphFixedRootTorus_le_torusGroup _ hy.1)),
           hx.2, hy.2, one_mul]⟩
       one_mem' := ⟨one_mem _, one_pow _⟩
       inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ },
      fun x => Iff.rfl⟩
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have h2f : ℓ ^ (2 * f) = (ℓ ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
  have hpq2 : p ∣ ℓ ^ (2 * f) - 1 := hpq.trans ⟨ℓ ^ f - 1, by
    rw [h2f]
    zify [Nat.one_le_pow 2 (ℓ ^ f) (by omega), hq1]
    ring⟩
  obtain ⟨hVcard, -, -, hCV, -, hNV, -, -, hscal, -, -, hζV⟩ :=
    triality_both_orientations_split_prime_plane_normalizers hℓ (f := 2 * f) (by omega) K₂
      (by rw [hK₂, h2f]; ring) (r := 2) (Or.inr rfl) σ₂ (fun c => by rw [hσ₂, h2f]; ring_nf)
      hp hp3 hpq2 V hV
  have hPV : Pl.map F = V := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨c, hc, rfl⟩
      exact (hV _).2 ⟨(Subgroup.mem_inf.1 (hPT c hc)).1, by rw [← map_pow, hPpow c hc, map_one]⟩
    · rw [hVcard, ← Nat.card_congr (Subgroup.equivMapOfInjective Pl F hF).toEquiv, hPcard]
  have hVP : ∀ x ∈ V, ∃ c ∈ Pl, F c = x := fun x hx => by
    rw [← hPV] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨c, hc, rfl⟩
  have hk₂ : Nat.card (trialityFixedField K₂ σ₂.toRingHom) = (ℓ ^ f) ^ 2 := by
    rw [← hL1, natCard_orbitField_K₂ hℓ hf hK₂ hσ₂,
      show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := (trialityFixedField K₂ σ₂.toRingHom)ˣ) p
    (by rw [Nat.card_units, hk₂, ← h2f]; exact hpq2)
  have hζ' : orderOf (trialityFixedUnit K₂ σ₂ ζ) = p := by
    rw [orderOf_injective _ (fun a b h => Units.ext (Subtype.ext (congrArg Units.val h))) ζ, hζ]
  have hz1 : trialityFixedUnit K₂ σ₂ ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hζ'
    exact hp.one_lt.ne hζ'
  obtain ⟨hVζ, -⟩ := hζV ζ hζ
  obtain ⟨x₁, hx₁⟩ : ∃ x, x = trialityOuterTorus K₂ σ₂ (trialityFixedUnit K₂ σ₂ ζ ^ 1) *
      trialityMiddleTorus K₂ σ₂ (ζ ^ 2) := ⟨_, rfl⟩
  have hx₁V : x₁ ∈ V := (hVζ _).2 ⟨1, 2, by rw [hx₁]; norm_num⟩
  have hx₁1 : x₁ ≠ 1 := by
    rw [hx₁, trialityOuter_mul_middle_pow_eq, ← rootDiagUnit_one]
    intro h
    have h2 : (trialityFixedUnit K₂ σ₂ ζ ^ 1 * trialityFixedUnit K₂ σ₂ ζ ^ 1 *
        trialityFixedUnit K₂ σ₂ ζ ^ 1)⁻¹ * (trialityFixedUnit K₂ σ₂ ζ ^ 2) ^ 2 = 1 :=
      congrFun (rootDiagUnit_injective h) i2
    exact hz1 (calc trialityFixedUnit K₂ σ₂ ζ = (trialityFixedUnit K₂ σ₂ ζ ^ 1 *
        trialityFixedUnit K₂ σ₂ ζ ^ 1 * trialityFixedUnit K₂ σ₂ ζ ^ 1)⁻¹ *
          (trialityFixedUnit K₂ σ₂ ζ ^ 2) ^ 2 := by group
      _ = 1 := h2)
  have hai₁ : ∀ a : Fin TwistTag.D4.tag.rank → K₂ˣ, x₁ = rootDiagUnit TwistTag.D4.tag a →
      a i0 = 1 := fun a ha => by
    rw [hx₁, trialityOuter_mul_middle_pow_eq] at ha
    rw [← rootDiagUnit_injective ha]
    change (trialityFixedUnit K₂ σ₂ ζ ^ 1) ^ 2 * (trialityFixedUnit K₂ σ₂ ζ ^ 2)⁻¹ = 1
    group
  obtain ⟨x₂, hx₂⟩ : ∃ x, x = trialityOuterTorus K₂ σ₂ (trialityFixedUnit K₂ σ₂ ζ ^ 2) *
      trialityMiddleTorus K₂ σ₂ (ζ ^ 3) := ⟨_, rfl⟩
  have hx₂V : x₂ ∈ V := (hVζ _).2 ⟨2, 3, by rw [hx₂]; norm_num⟩
  have hx₂1 : x₂ ≠ 1 := by
    rw [hx₂, trialityOuter_mul_middle_pow_eq, ← rootDiagUnit_one]
    intro h
    have h0 : (trialityFixedUnit K₂ σ₂ ζ ^ 2) ^ 2 * (trialityFixedUnit K₂ σ₂ ζ ^ 3)⁻¹ = 1 :=
      congrFun (rootDiagUnit_injective h) i0
    exact hz1 (calc trialityFixedUnit K₂ σ₂ ζ =
        (trialityFixedUnit K₂ σ₂ ζ ^ 2) ^ 2 * (trialityFixedUnit K₂ σ₂ ζ ^ 3)⁻¹ := by group
      _ = 1 := h0)
  have hai₂ : ∀ a : Fin TwistTag.D4.tag.rank → K₂ˣ, x₂ = rootDiagUnit TwistTag.D4.tag a →
      a i2 = 1 := fun a ha => by
    rw [hx₂, trialityOuter_mul_middle_pow_eq] at ha
    rw [← rootDiagUnit_injective ha]
    change (trialityFixedUnit K₂ σ₂ ζ ^ 2 * trialityFixedUnit K₂ σ₂ ζ ^ 2 *
      trialityFixedUnit K₂ σ₂ ζ ^ 2)⁻¹ * (trialityFixedUnit K₂ σ₂ ζ ^ 3) ^ 2 = 1
    group
  obtain ⟨c₁, hc₁, rfl⟩ := hVP x₁ hx₁V
  obtain ⟨c₂, hc₂, rfl⟩ := hVP x₂ hx₂V
  have hc₁1 : c₁ ≠ 1 := fun h => hx₁1 (by rw [h, map_one])
  have hc₂1 : c₂ ≠ 1 := fun h => hx₂1 (by rw [h, map_one])
  have hx₁p : orderOf (F c₁) = p := orderOf_eq_prime ((hV _).1 hx₁V).2 hx₁1
  have hx₂p : orderOf (F c₂) = p := orderOf_eq_prime ((hV _).1 hx₂V).2 hx₂1
  obtain ⟨hRq₁, hinj₁, -, -, -, htr₁, hcent₁⟩ := qplus_simple_orbit_derived hℓ hf hK hK₂ hσ hσ₂ hτ
    hg hzg hp hp3 hpq (hPT c₁ hc₁) hx₁p (b := ⟨0, by decide⟩) (by decide) hai₁
  obtain ⟨hRq₂, hinj₂, -, -, -, -, hcent₂⟩ := qplus_simple_orbit_derived hℓ hf hK hK₂ hσ hσ₂ hτ
    hg hzg hp hp3 hpq (hPT c₂ hc₂) hx₂p (b := ⟨1, by decide⟩) (by decide) hai₂
  have hderiv : ∀ c, (⁅centralizer ({c} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      centralizer ({c} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map F =
      ⁅trialityConjImage K σ.toRingHom g ⊓ centralizer {F c},
        trialityConjImage K σ.toRingHom g ⊓ centralizer {F c}⁆ := fun c => by
    rw [Subgroup.map_commutator, map_centralizer_singleton_of_injective hF hrange c]
  have hquasi : ∀ c, CFSG.IsQuasisimple (⁅trialityConjImage K σ.toRingHom g ⊓ centralizer {F c},
      trialityConjImage K σ.toRingHom g ⊓ centralizer {F c}⁆ :
        Subgroup (ModGL TwistTag.D4.tag K₂)) →
      CFSG.IsQuasisimple (⁅centralizer ({c} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        centralizer ({c} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ :
          Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := fun c hq =>
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ((Subgroup.equivMapOfInjective _ F hF).trans
      (MulEquiv.subgroupCongr (hderiv c))).symm hq
  rw [eq_bot_iff]
  intro η hη
  have hfixP : ∀ c ∈ Pl, (η : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) c = c :=
    fun c hc => apply_eq_of_mem_thetaT hinj hB hη (hPE c hc)
  have hfix₁ := apply_eq_of_mem_thetaT_of_isQuasisimple hinj hB hp hη (hPE c₁ hc₁) hc₁1
    (hquasi c₁ hRq₁)
  have hfix₂ := apply_eq_of_mem_thetaT_of_isQuasisimple hinj hB hp hη (hPE c₂ hc₂) hc₂1
    (hquasi c₂ hRq₂)
  obtain ⟨y, δ, hηyδ⟩ := triality_exists_normal_form hℓ hf K hK σ hσ η
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨j, hj⟩ := exists_eq_frobenius_pow hℓ (by omega : 1 ≤ 3 * f) hK3 δ
  obtain ⟨δ₂, hδ₂⟩ := exists_frobenius_pow (L := K₂) (ℓ := ℓ) j
  have hδext : ∀ k, δ₂ (algebraMap K K₂ k) = algebraMap K K₂ (δ k) := fun k => by
    rw [hδ₂, hj, map_pow]
  have hδσ : ∀ c, δ₂ (σ₂.toRingHom c) = σ₂.toRingHom (δ₂ c) := fun c => by
    change δ₂ (σ₂ c) = σ₂ (δ₂ c)
    rw [hδ₂, hσ₂, hσ₂, hδ₂, pow_right_comm]
  obtain ⟨v, hvdef⟩ : ∃ v : ModGL TwistTag.D4.tag K₂, v = F y * (u * g) *
      (Units.map (entrywiseHom δ₂.toRingHom) (u * g))⁻¹ := ⟨_, rfl⟩
  have hFη : ∀ c, F ((η : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) c) =
      twistedEntrywise v δ₂.toRingHom (F c) := fun c => by
    rw [hηyδ, hvdef, twistedEntrywise_apply, hFdef]
    exact map_fieldActor_conj_eq (u * g) y δ δ₂ hδext c
  have hug : u * g ∈ graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom := mul_mem (hΓC hu) hg
  have hδug : Units.map (entrywiseHom δ₂.toRingHom) (u * g) ∈
      graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom := by
    have h1 := (fieldActor (t := TwistTag.D4) σ₂ δ₂ ⟨u * g, hug⟩).2
    rwa [coe_fieldActor] at h1
  have hvC : v ∈ graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom := by
    rw [hvdef]
    exact mul_mem (mul_mem (hΓC (hFΓ y)) hug) (inv_mem hδug)
  have hvV : ∀ x ∈ V, v⁻¹ * x * v = x ^ (ℓ ^ j) := fun x hx => by
    obtain ⟨c, hc, rfl⟩ := hVP x hx
    have h1 := hFη c
    rw [hfixP c hc, twistedEntrywise_apply, units_map_entrywiseHom_of_mem_torusGroup
      (F := δ₂.toRingHom) (fun c => hδ₂ c)
      (graphFixedRootTorus_le_torusGroup _ (Subgroup.mem_inf.1 (hPT c hc)).1)] at h1
    calc v⁻¹ * F c * v = v⁻¹ * (v * F c ^ (ℓ ^ j) * v⁻¹) * v := by rw [← h1]
      _ = F c ^ (ℓ ^ j) := by group
  have hvN : v⁻¹ ∈ graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom ⊓
      Subgroup.normalizer (V : Set (ModGL TwistTag.D4.tag K₂)) := by
    refine Subgroup.mem_inf.2 ⟨inv_mem hvC, Subgroup.mem_normalizer_iff.2 fun x => ?_⟩
    rw [inv_inv]
    constructor
    · intro hx
      rw [hvV x hx]
      exact pow_mem hx _
    · intro hx
      have hsurj : Function.Surjective (fun z : V =>
          (⟨v⁻¹ * z * v, by rw [hvV z z.2]; exact pow_mem z.2 _⟩ : V)) :=
        Finite.surjective_of_injective fun z z' h => Subtype.ext (by
          have h1 := congrArg Subtype.val h
          simpa using h1)
      obtain ⟨z, hz⟩ := hsurj ⟨_, hx⟩
      have h1 : (z : ModGL TwistTag.D4.tag K₂) = x := by
        have h2 := congrArg Subtype.val hz
        simpa using h2
      rw [← h1]
      exact z.2
  obtain ⟨h₀, hh₀, w, hw, hvw⟩ := hNV v⁻¹ hvN
  have hh₀T := graphFixedRootTorus_le_torusGroup _ hh₀
  have hwscal : ∀ x ∈ V, canonicalRep (coxeterSystem TwistTag.D4.tag) K₂ w * x *
      (canonicalRep (coxeterSystem TwistTag.D4.tag) K₂ w)⁻¹ = x ^ ((ℓ ^ j : ℕ) : ℤ) :=
    fun x hx => by
      have hn : canonicalRep (coxeterSystem TwistTag.D4.tag) K₂ w = h₀⁻¹ * v⁻¹ := by
        rw [hvw]
        group
      have hxT : x ^ (ℓ ^ j) ∈ torusGroup TwistTag.D4.tag K₂ :=
        pow_mem (graphFixedRootTorus_le_torusGroup _ ((hV x).1 hx).1) _
      rw [hn, zpow_natCast]
      calc h₀⁻¹ * v⁻¹ * x * (h₀⁻¹ * v⁻¹)⁻¹ = h₀⁻¹ * (v⁻¹ * x * v) * h₀ := by group
        _ = h₀⁻¹ * x ^ (ℓ ^ j) * h₀ := by rw [hvV x hx]
        _ = x ^ (ℓ ^ j) := by
          rw [commute_of_mem_torusGroup (inv_mem hh₀T) hxT, inv_mul_cancel_right]
  obtain ⟨M, hM⟩ : ∃ M : GL (Fin 2) (orbitField TwistTag.D4 K₂ σ₂.toRingHom ⟨0, by decide⟩), ∀ A,
      orbitConjRankOneHom TwistTag.D4 K₂ σ₂.toRingHom 1 ⟨0, by decide⟩
          (semilinearConj M (orbitFieldRestrict δ₂ hδσ ⟨0, by decide⟩) A) =
        twistedEntrywise v δ₂.toRingHom
          (orbitConjRankOneHom TwistTag.D4 K₂ σ₂.toRingHom 1 ⟨0, by decide⟩ A) := by
    rcases hscal w hw _ hwscal with rfl | hwneg
    · have hv : v = h₀⁻¹ := by
        rw [← inv_inv v, hvw, canonicalRep_one, mul_one]
      have hvT : v ∈ graphFixedTorus TwistTag.D4 K₂ σ₂.toRingHom := by
        rw [hv]
        exact (Subgroup.mem_inf.1 (inv_mem hh₀)).1
      exact exists_semilinearConj_orbitConjRankOneHom_of_torus hδσ hvT (one_mem _) _
    · have hv : v = (canonicalRep (coxeterSystem TwistTag.D4.tag) K₂ w)⁻¹ * h₀⁻¹ := by
        rw [← inv_inv v, hvw, mul_inv_rev]
      have hz : v ∈ monomialSubgroup TwistTag.D4.tag K₂ := by
        rw [hv]
        exact mul_mem (inv_mem (canonicalRep_mem_monomialSubgroup K₂ w))
          (inv_mem (torusGroup_le_monomialSubgroup hh₀T))
      have hmaps : MapsRootLines v (w⁻¹ * 1) := by
        rw [hv]
        exact (mapsRootLines_canonicalRep (R := K₂) w).inv.mul
          (mapsRootLines_of_mem_torusGroup (inv_mem hh₀T))
      have hwv : ∀ x : Fin TwistTag.D4.tag.rank → ℤ,
          weylQuotientHom TwistTag.D4.tag K₂ ⟨v, hz⟩ • x = -x := fun x => by
        rw [weylQuotientHom_eq hmaps, mul_one, inv_smul_eq_neg hwneg]
      exact exists_semilinearConj_orbitConjRankOneHom hδσ hz hwv
        (graphFixedRootGroup_le _ _ _ hvC) (one_mem _) _ hinj₁
  have hψ₁ : ∀ r ∈ (⁅trialityConjImage K σ.toRingHom g ⊓ centralizer {F c₁},
      trialityConjImage K σ.toRingHom g ⊓ centralizer {F c₁}⁆ :
        Subgroup (ModGL TwistTag.D4.tag K₂)), twistedEntrywise v δ₂.toRingHom r = r := by
    intro r hr
    rw [← hderiv c₁] at hr
    obtain ⟨c, hc, rfl⟩ := hr
    rw [← hFη c, hfix₁ c hc]
  have hδ1 : ∀ k, δ k = k := by
    intro k
    have hk : algebraMap K K₂ k ∈ (orbitFieldFixed σ₂.toRingHom τ.toRingHom ⟨0, by decide⟩).map
        (orbitField TwistTag.D4 K₂ σ₂.toRingHom ⟨0, by decide⟩).subtype := by
      rw [map_orbitFieldFixed_zero hℓ hK hK₂ hσ₂ hτ]
      exact ⟨k, rfl⟩
    obtain ⟨c, hc, hck⟩ := Subfield.mem_map.1 hk
    have hmem : algebraMap (orbitFieldFixed σ₂.toRingHom τ.toRingHom ⟨0, _⟩)
        (orbitField TwistTag.D4 K₂ σ₂.toRingHom ⟨0, _⟩) ⟨c, hc⟩ ∈
          Set.range (algebraMap (orbitFieldFixed σ₂.toRingHom τ.toRingHom ⟨0, _⟩)
            (orbitField TwistTag.D4 K₂ σ₂.toRingHom ⟨0, _⟩)) := ⟨_, rfl⟩
    rw [← htr₁] at hmem
    obtain ⟨A, hA, hAtr⟩ := hmem
    beta_reduce at hAtr
    have h2 := fixes_trace_of_semilinearConj hinj₁ hM hψ₁ (by exact hA)
    rw [hAtr] at h2
    have h3 := congrArg Subtype.val h2
    rw [coe_orbitFieldRestrict] at h3
    change δ₂ (c : K₂) = c at h3
    rw [show (c : K₂) = algebraMap K K₂ k from hck, hδext] at h3
    exact (algebraMap K K₂).injective h3
  have hηy : (η : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = MulAut.conj y := by
    rw [hηyδ, show δ = 1 from RingEquiv.ext hδ1, fieldActor_one, mul_one]
  have hyfix : ∀ c, (η : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) c = c →
      y * c * y⁻¹ = c := fun c h => by
    rw [hηy, MulAut.conj_apply] at h
    exact h
  have hFyV : F y ∈ graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom ⊓
      Subgroup.centralizer (V : Set (ModGL TwistTag.D4.tag K₂)) := by
    refine Subgroup.mem_inf.2 ⟨hΓC (hFΓ y), Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    obtain ⟨c, hc, rfl⟩ := hVP x hx
    rw [← map_mul, ← map_mul]
    congr 1
    calc c * y = (y * c * y⁻¹) * y := by rw [hyfix c (hfixP c hc)]
      _ = y * c := by group
  rw [hCV] at hFyV
  have hFyT : F y ∈ graphFixedTorus TwistTag.D4 K₂ σ₂.toRingHom := (Subgroup.mem_inf.1 hFyV).1
  have hcentR : ∀ c₀, (∀ r ∈ (⁅centralizer ({c₀} : Set (graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom)), centralizer ({c₀} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
          (η : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) r = r) →
      ∀ r ∈ (⁅trialityConjImage K σ.toRingHom g ⊓ centralizer {F c₀},
        trialityConjImage K σ.toRingHom g ⊓ centralizer {F c₀}⁆ :
          Subgroup (ModGL TwistTag.D4.tag K₂)), F y * r * (F y)⁻¹ = r := fun c₀ hfix r hr => by
    rw [← hderiv c₀] at hr
    obtain ⟨c, hc, rfl⟩ := hr
    rw [← map_inv, ← map_mul, ← map_mul, hyfix c (hfix c hc)]
  have hQ₁ := conj_orbitConjRankOneHom_eq_self_of_centralizer hFyT (one_mem _) hinj₁ hcent₁
    (hcentR c₁ hfix₁)
  have hQ₂ := conj_orbitConjRankOneHom_eq_self_of_centralizer hFyT (one_mem _) hinj₂ hcent₂
    (hcentR c₂ hfix₂)
  have hrangeΦ : ∀ b, (orbitConjRankOneHom TwistTag.D4 K₂ σ₂.toRingHom 1 b).range =
      orbitRankOneGroup TwistTag.D4 K₂ σ₂.toRingHom b := fun b => by
    rw [range_orbitConjRankOneHom (one_mem _) b, orbitRankOneGroup_eq_graphFixedRootPair]
  have hle : graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom ≤ centralizer {F y} := by
    rw [graphFixedRootGroup_D4_eq_sup K₂ σ₂]
    refine sup_le ?_ ?_
    · rw [← hrangeΦ]
      rintro _ ⟨A, rfl⟩
      exact mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 (hQ₁ A)).symm
    · rw [← hrangeΦ]
      rintro _ ⟨A, rfl⟩
      exact mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 (hQ₂ A)).symm
  have hyZ : y ∈ Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply hF
    rw [map_mul, map_mul]
    exact mem_centralizer_singleton_iff.1 (hle (hΓC (hFΓ c)))
  rw [hZ, Subgroup.mem_bot] at hyZ
  rw [Subgroup.mem_bot]
  exact Subtype.ext (by rw [hηy, hyZ, map_one]; rfl)

end CFSG.RankThree.Chevalley
end
