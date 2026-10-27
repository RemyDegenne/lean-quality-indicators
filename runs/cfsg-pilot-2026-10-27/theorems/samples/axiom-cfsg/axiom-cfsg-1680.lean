public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1920

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18 (le_pCoreOf_of_normal)

open CFSG.LocalAnalysis.GLTheoremB.Prop95I1921

open CFSG.LieType.ChevTwo (Chev2CoreCent Chev2KDOut autCentralizer)

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)

open scoped commutatorElement

theorem input19_20_3_of_kdout_corecent (hKD : Chev2KDOut) (hCore : Chev2CoreCent)
    (hS3 : Input19_20_3Core) (hZ1 : OmegaFourComponentCentre) : Input19_20_3 := by
  intro X _ _ p hp hp2 K hK hCh D Sd hfam n ε hn hΩ hnc
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDp : ∀ x ∈ D, x ^ p = 1 := hfam.elemAbelian.2
  have hZK : Subgroup.center ↥K = ⊥ := center_eq_bot_of_omega hZ1 hK hn ε hΩ
  have hB1 : ∀ d ∈ D, d ≠ 1 →
      pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) ≤ Subgroup.normalizer (K : Set X) :=
    fun d hd _ => pCoreOf_le_normalizer_of_chev hCore hp hp2 hK hCh (hDp d hd)
  haveI : IsSimpleGroup (Kbar K) := hK.2.2.2
  set D1 : Subgroup ↥(Subgroup.normalizer (K : Set X)) :=
    D.subgroupOf (Subgroup.normalizer (K : Set X)) with hD1def
  have hD1p : IsPGroup p D1 := isPGroup_subgroupOf_of_exponent hDp
  have hab : ∀ a ∈ D1, ∀ b ∈ D1, a * b = b * a := by
    intro a ha b hb
    have := isMulCommutative_iff.1 hfam.elemAbelian.1 ⟨(a : X), Subgroup.mem_subgroupOf.1 ha⟩
      ⟨(b : X), Subgroup.mem_subgroupOf.1 hb⟩
    have h : (a : X) * (b : X) = (b : X) * (a : X) := congrArg Subtype.val this
    exact Subtype.ext h
  have hD1exp : ∀ e ∈ D1, e ^ p = 1 := fun e he =>
    Subtype.ext (by simpa using hDp (e : X) (Subgroup.mem_subgroupOf.1 he))
  have hKY : Kinn K ≤ Yg K D1 := Kinn_le_Yg K D1
  have hfamY := signalizerFamilyYg (K := K) (D1 := D1) hab hD1exp
  haveI : (KhY K (Yg K D1)).Normal := inferInstance
  have hint := (input19_20_2CoreStrong_of hKD hCore) ↥(Yg K D1) (KhY K (Yg K D1))
    (isSimpleGroup_KhY hK hKY) (KhY_nonabelian hK hKY) (isChevTwo_KhY hK hKY hCh)
    (centralizer_KhY hK hKY) p hp hp2 (DYg K D1) (SYg K D1) hfamY
  set σ := sigmaFam (DYg K D1) (SYg K D1) with hσdef
  have htriv : ∀ (s : X) (hsN : s ∈ Subgroup.normalizer (K : Set X)),
      s ∈ Subgroup.centralizer (K : Set X) →
        rhoK K ⟨s, hsN⟩ ∈ σ.map (Yg K D1).subtype := by
    intro s hsN hsC
    have h1 : rhoK K ⟨s, hsN⟩ = 1 := (rhoK_eq_one_iff hK hsN).2 hsC
    rw [h1]
    exact (σ.map (Yg K D1).subtype).one_mem
  have hkey : ∀ d ∈ D, d ≠ 1 → ∀ s ∈ Sd d, ∃ hsN : s ∈ Subgroup.normalizer (K : Set X),
      rhoK K ⟨s, hsN⟩ ∈ σ.map (Yg K D1).subtype := by
    intro d hd hd1 s hs
    have hsT := hfam.le_pCore d hd hd1 hs
    have hsN := hB1 d hd hd1 hsT
    refine ⟨hsN, ?_⟩
    by_cases hdN : d ∈ Subgroup.normalizer (K : Set X)
    · by_cases hdC : d ∈ Subgroup.centralizer (K : Set X)
      · exact htriv s hsN (pCoreOf_le_centralizer_of_mem_centralizer hK hdC (hB1 d hd hd1) hsT)
      · set dN : ↥(Subgroup.normalizer (K : Set X)) := ⟨d, hdN⟩ with hdNdef
        have hdD1 : dN ∈ D1 := Subgroup.mem_subgroupOf.2 hd
        have hdp : dN ^ p = 1 := hD1exp dN hdD1
        have hsmem : (⟨s, hsN⟩ : ↥(Subgroup.normalizer (K : Set X))) ∈
            pCoreOf 2 (Subgroup.centralizer ({dN} : Set ↥(Subgroup.normalizer (K : Set X)))) :=
          subgroupOf_pCoreOf_le hdN (Subgroup.mem_subgroupOf.2 hsT)
        have hsY := rho_pCore_mem_Yg hKD hCore hK hCh hp hp2 hD1p hab hdD1 hdp hsmem
        have h1 : (⟨rhoK K ⟨s, hsN⟩, hsY⟩ : ↥(Yg K D1)) ∈
            SYg K D1 ⟨rhoK K dN, rho_mem_Yg_of_mem hdD1⟩ :=
          rho_pCore_subgroupOf_le hK hZK hab hdD1
            (Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem _ hsmem))
        have hdh1 : (⟨rhoK K dN, rho_mem_Yg_of_mem hdD1⟩ : ↥(Yg K D1)) ≠ 1 := fun h =>
          hdC ((rhoK_eq_one_iff hK hdN).1 (congrArg Subtype.val h))
        have hdhD : (⟨rhoK K dN, rho_mem_Yg_of_mem hdD1⟩ : ↥(Yg K D1)) ∈ DYg K D1 :=
          Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem _ hdD1)
        have h2 : (⟨rhoK K ⟨s, hsN⟩, hsY⟩ : ↥(Yg K D1)) ∈ σ :=
          (le_iSup₂_of_le _ hdhD (le_iSup_of_le hdh1 le_rfl) :
            SYg K D1 ⟨rhoK K dN, rho_mem_Yg_of_mem hdD1⟩ ≤ σ) h1
        exact ⟨_, h2, rfl⟩
    · exact htriv s hsN (le_centralizer_of_not_mem_normalizer' hp hK (hDp d hd) hdN
        (hB1 d hd hd1) le_rfl hsT)
  have hSdS : ∀ d ∈ D, d ≠ 1 → Sd d ≤ sigmaFam D Sd := fun d hd hd1 =>
    le_iSup_of_le d (le_iSup_of_le hd (le_iSup_of_le hd1 le_rfl))
  have hpull : ∀ s ∈ sigmaFam D Sd, ∃ hsN : s ∈ Subgroup.normalizer (K : Set X),
      rhoK K ⟨s, hsN⟩ ∈ σ.map (Yg K D1).subtype := by
    have hgen : ∀ T : Subgroup X, (∀ d ∈ D, d ≠ 1 → Sd d ≤ T) → sigmaFam D Sd ≤ T := by
      intro T hT
      unfold sigmaFam
      exact iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => hT d hd hd1
    have hle := hgen
      (((σ.map (Yg K D1).subtype).comap (rhoK K)).map (Subgroup.normalizer (K : Set X)).subtype)
      (fun d hd hd1 s hs => by
        obtain ⟨hsN, hmem⟩ := hkey d hd hd1 s hs
        exact ⟨⟨s, hsN⟩, Subgroup.mem_comap.2 hmem, rfl⟩)
    intro s hs
    obtain ⟨n, hn, rfl⟩ := hle hs
    exact ⟨n.2, hn⟩
  obtain ⟨d₀, hd₀, hd₀1, s₀, hs₀, hs₀C⟩ : ∃ d₀ ∈ D, d₀ ≠ 1 ∧ ∃ s₀ ∈ Sd d₀,
      s₀ ∉ Subgroup.centralizer (K : Set X) := by
    by_contra hcon
    push Not at hcon
    apply hnc
    unfold sigmaFam
    exact iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 s hs => hcon d hd hd1 s hs
  have hs₀S : s₀ ∈ sigmaFam D Sd := hSdS d₀ hd₀ hd₀1 hs₀
  obtain ⟨hsN₀, hmem₀⟩ := hpull s₀ hs₀S
  have hσne : σ ≠ ⊥ := by
    intro h
    obtain ⟨y, hyσ, hy⟩ := Subgroup.mem_map.1 hmem₀
    rw [h, Subgroup.mem_bot] at hyσ
    rw [hyσ] at hy
    exact hs₀C ((rhoK_eq_one_iff hK hsN₀).1 (by simpa using hy.symm))
  have hΩY : IsOmegaTwo ε (n + 1) ↥(KhY K (Yg K D1)) :=
    isOmegaTwo_of_mulEquiv (iotaY hK hZK hKY) ε (n + 1) hΩ
  obtain ⟨hact, hfpf⟩ := hS3 ↥(Yg K D1) (KhY K (Yg K D1)) (isSimpleGroup_KhY hK hKY)
    (centralizer_KhY hK hKY) p hp hp2 (DYg K D1) (SYg K D1) hfamY hint.1 n ε hn hΩY hσne
  refine ⟨?_, hfpf⟩
  refine actsAsTransvectionAt_transport ε n (sigmaFam D Sd) K σ (KhY K (Yg K D1))
    (iotaY hK hZK hKY) ?_ ?_ hact
  · intro ψ hψ
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.1 hψ
    obtain ⟨w, hw, hwS, rfl⟩ := mem_inducedAutGroup.1 hφ
    obtain ⟨hwN, hmem⟩ := hpull w hwS
    obtain ⟨y, hyσ, hyw⟩ := Subgroup.mem_map.1 hmem
    have hwY : rhoK K ⟨w, hw⟩ ∈ Yg K D1 := by
      have := y.2
      rwa [show (y : MulAut (Kbar K)) = rhoK K ⟨w, hwN⟩ from hyw] at this
    have hyeq : (⟨rhoK K ⟨w, hw⟩, hwY⟩ : ↥(Yg K D1)) = y := Subtype.ext hyw.symm
    refine mem_inducedAutGroup.2 ⟨⟨rhoK K ⟨w, hw⟩, hwY⟩,
      Subgroup.le_normalizer_of_normal (Subgroup.mem_top _), ?_, ?_⟩
    · rw [hyeq]
      exact hyσ
    · exact (congr_iotaY_normalizerMonoidHom hK hZK hKY ⟨w, hw⟩ hwY).symm
  · intro h
    have hmem : (MulAut.congr (iotaY hK hZK hKY)).toMonoidHom
        (K.normalizerMonoidHom ⟨s₀, hsN₀⟩) ∈
        (inducedAutGroup (sigmaFam D Sd) K).map (MulAut.congr (iotaY hK hZK hKY)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (mem_inducedAutGroup.2 ⟨s₀, hsN₀, hs₀S, rfl⟩)
    rw [h, Subgroup.mem_bot] at hmem
    have h1 : K.normalizerMonoidHom ⟨s₀, hsN₀⟩ = 1 :=
      (MulAut.congr (iotaY hK hZK hKY)).injective (hmem.trans (map_one _).symm)
    exact hs₀C ((normalizerMonoidHom_eq_one_iff hsN₀).1 h1)

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1920
end
