namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_residue_classify_eq_of_map_residue_eq_rigidDataH1Pow

set_option autoImplicit false

universe u

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

attribute [local instance] MvPolynomial.gradedAlgebra

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

open CategoryTheory AlgebraicGeometry

theorem solution
    (q : ℕ) [Fact q.Prime] (ℓg M' : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) [NeZero M'] (hℓgM' : ℓg ∣ M')
    (A₀ : Type) [CommRing A₀]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)

    (x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)

    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra A₀ R] (ι : P₀.B₀ →ₐ[A₀] R)
    (k : Type) [Field k] [CharP k q] (hℓk : ((ℓg : ℕ) : k) ≠ 0) (hM'k : ((M' : ℕ) : k) ≠ 0)
    (resR : R →+* k) (hresR : Function.Surjective resR) (hkerR : RingHom.ker resR = maximalIdeal R)

    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    [Algebra W₀ R] [Algebra A₀ W₀] [IsScalarTower A₀ W₀ R]
    (hresR₀ : ∀ w : W₀, resR (algebraMap W₀ R w) = res₀ w)

    (hfac : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        [Algebra A₀ T] [IsScalarTower A₀ W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ φ : P₀.B₀ →ₐ[A₀] T, (∀ b : P₀.B₀, resT (φ b) = resR (ι b)) →
          ∃! Φ : R →ₐ[W₀] T, (∀ r : R, resT (Φ r) = resR r) ∧ ∀ b : P₀.B₀, Φ (ι b) = φ b)

    (F : FormalGroup R) [F.IsComm]
    (hFW : F.toPowerSeries =
      (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve).formalGroupLawFixed)

    (F₀ : FormalGroup k) [F₀.IsComm]
    (hF₀W : F₀.toPowerSeries =
      ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve).map resR).formalGroupLawFixed)
    (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (χP χQ : OriginChartRing (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve) →+* R)
    (hP : ReducesToOrigin ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.P χP (maximalIdeal R))
    (hQ : ReducesToOrigin ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.Q χQ (maximalIdeal R))
    (hD : F.IsDrinfeldBasisAdic (maximalIdeal R) q (originParam χP) (originParam χQ))
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
    [Algebra A₀ T] [IsScalarTower A₀ W₀ T]
    (resT : T →+* k) (hsT : Function.Surjective resT) (hkT : RingHom.ker resT = maximalIdeal T)
    (hT₀ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w)
    (yT : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T)
    (χPT χQT : OriginChartRing yT.level.2.2.curve →+* T)
    (hPT : ReducesToOrigin yT.level.2.2.P χPT (maximalIdeal T))
    (hQT : ReducesToOrigin yT.level.2.2.Q χQT (maximalIdeal T))
    (hcurve : yT.curve.map resT = (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve).map resR)
    (hlev : yT.level.2.1.map resT = (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.1).map resR)
    (hker : (∀ pf : ↥M'.primeFactors, (yT.level.1 pf).map resT = (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.1 pf).map resR)) :
    ∀ b : P₀.B₀,
      resT (P₀.classify (Quot.mk _ yT : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt T) b) = resR (ι b) := by
  classical
  intro b

  letI : Algebra A₀ k := (res₀.comp (algebraMap A₀ W₀)).toAlgebra
  let ρT : T →ₐ[A₀] k :=
    { toRingHom := resT
      commutes' := fun a => by
        show resT (algebraMap A₀ T a) = res₀ (algebraMap A₀ W₀ a)
        rw [IsScalarTower.algebraMap_apply A₀ W₀ T, hT₀] }
  let ρR : R →ₐ[A₀] k :=
    { toRingHom := resR
      commutes' := fun a => by
        show resR (algebraMap A₀ R a) = res₀ (algebraMap A₀ W₀ a)
        rw [IsScalarTower.algebraMap_apply A₀ W₀ R, hresR₀] }

  haveI : IsAdicComplete (maximalIdeal k) k :=
    IsAdicComplete.of_isNilpotent ⟨1, by rw [pow_one, Ideal.zero_eq_bot]; exact Ideal.eq_bot_of_prime _⟩
  have hmT : (maximalIdeal T).map resT ≤ maximalIdeal k := by
    rw [Ideal.map_le_iff_le_comap]; intro t ht
    rw [← hkT, RingHom.mem_ker] at ht
    rw [Ideal.mem_comap, ht]; exact zero_mem _
  have hmR : (maximalIdeal R).map resR ≤ maximalIdeal k := by
    rw [Ideal.map_le_iff_le_comap]; intro t ht
    rw [← hkerR, RingHom.mem_ker] at ht
    rw [Ideal.mem_comap, ht]; exact zero_mem _

  obtain ⟨hcT, hpinT⟩ := h𝒯.2 T k ρT yT.level.2.2
  obtain ⟨hcR, hpinR⟩ := h𝒯.2 R k ρR ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2
  obtain ⟨χP₁, hP₁, hzP₁⟩ := GCResidue.aux_bc_originParam _ resT _ hcT _ χPT _ hPT _
    (fun φ hφ hco => (hpinT φ hφ hco).1)
  obtain ⟨χQ₁, hQ₁, hzQ₁⟩ := GCResidue.aux_bc_originParam _ resT _ hcT _ χQT _ hQT _
    (fun φ hφ hco => (hpinT φ hφ hco).2)
  obtain ⟨χP₂, hP₂, hzP₂⟩ := GCResidue.aux_bc_originParam _ resR _ hcR _ χP _ hP _
    (fun φ hφ hco => (hpinR φ hφ hco).1)
  obtain ⟨χQ₂, hQ₂, hzQ₂⟩ := GCResidue.aux_bc_originParam _ resR _ hcR _ χQ _ hQ _
    (fun φ hφ hco => (hpinR φ hφ hco).2)
  have hyc : yT.level.2.2.curve = yT.curve := yT.isLevel.1.2.2.1
  have hxc : ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve = ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).curve := ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).isLevel.1.2.2.1
  have hz : 𝒯.map ρT yT.level.2.2 = 𝒯.map ρR ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2 := by
    refine GCResidue.rawDrinfeldPair_eq _ _ ?_ χP₁ χQ₁ χP₂ χQ₂
      (GCResidue.reducesToOrigin_mono _ _ hmT hP₁) (GCResidue.reducesToOrigin_mono _ _ hmT hQ₁)
      (GCResidue.reducesToOrigin_mono _ _ hmR hP₂) (GCResidue.reducesToOrigin_mono _ _ hmR hQ₂) ?_ ?_
    · rw [hcT, hcR]
      show yT.level.2.2.curve.map resT = ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve.map resR
      rw [hyc]; exact hcurve
    · rw [hzP₁, hzP₂]
      show resT (originParam χPT) = resR (originParam χP)
      have h1 : originParam χPT ∈ RingHom.ker resT := hkT.symm ▸ hPT.2.1
      have h2 : originParam χP ∈ RingHom.ker resR := hkerR.symm ▸ hP.2.1
      rw [RingHom.mem_ker] at h1 h2
      rw [h1, h2]
    · rw [hzQ₁, hzQ₂]
      show resT (originParam χQT) = resR (originParam χQ)
      have h1 : originParam χQT ∈ RingHom.ker resT := hkT.symm ▸ hQT.2.1
      have h2 : originParam χQ ∈ RingHom.ker resR := hkerR.symm ▸ hQ.2.1
      rw [RingHom.mem_ker] at h1 h2
      rw [h1, h2]

  have hraw : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ρT yT = (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ρR ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x) := by
    refine ModularCurve.LevelComponent.Raw.ext' ?_ ?_
    · show yT.curve.map resT = ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).curve.map resR
      rw [hcurve, hxc]
    · refine Prod.ext ?_ (Prod.ext ?_ hz)
      · exact funext hker
      · show yT.level.2.1.map resT = ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.1.map resR
        exact hlev

  have hpt : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map (ρT.comp (P₀.classify (Quot.mk _ yT : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt T))) P₀.univ =
      (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map (ρR.comp ι) P₀.univ := by
    rw [(rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map_comp, P₀.map_classify, (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map_comp, ← hx]
    show (Quot.mk _ ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ρT yT) : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt k) = Quot.mk _ ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ρR ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x))
    rw [hraw]
  have heq : ρT.comp (P₀.classify (Quot.mk _ yT : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt T)) = ρR.comp ι :=
    (P₀.classify_unique _ _ hpt).trans (P₀.classify_unique _ _ rfl).symm
  exact AlgHom.congr_fun heq b

end P2MW.S_ModularCurve_LevelModuliPackageAbs_residue_classify_eq_of_map_residue_eq_rigidDataH1Pow
