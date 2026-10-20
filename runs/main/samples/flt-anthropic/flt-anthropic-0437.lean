namespace P2MW.S_ModularCurve_FullLevel_exists_reads_of_goodPt_twoChartIntegralModel_of_eq_three

attribute [-instance] CuspForm.GammaH_finiteIndex ValuationSubring.instIsAlgClosedResidueField

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup

open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory.Limits

universe u

namespace E140CR

open AlgebraicCurve.TwoChartIntegralModel E137 IsLocalRing

theorem exists_place_reads_fin {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {K Fbar : Type*} [Field K] [Field Fbar] [Algebra K Fbar] (t : Fbar)
    [FiniteDimensional ↥(IntermediateField.adjoin K ({t} : Set Fbar)) Fbar]
    (W : Subring F) (res : W →+* Fbar)
    (hFin : ∀ b : ↥(chartAlgFin R F j), (b : F) ∈ W)
    (hK : ∀ c : K, ∃ a : R, ∃ h : algebraMap R F a ∈ W, res ⟨_, h⟩ = algebraMap K Fbar c)
    (y : ↥(XFin R F j))
    (hunit : ∀ b : ↥(chartAlgFin R F j), b ∉ y.asIdeal → IsUnit (⟨(b : F), hFin b⟩ : W))
    (hng : ∃ b : ↥(chartAlgFin R F j), b ∈ y.asIdeal ∧ res ⟨(b : F), hFin b⟩ ≠ 0) :
    ∃ Q : AlgebraicCurve.Place K Fbar, ∀ f : F, InStalkG j ((ιFin R F j).base y) f →
      ∃ hW : f ∈ W, res ⟨f, hW⟩ ∈ Q.toValuationSubring ∧
        (res ⟨f, hW⟩ ∈ Q.toValuationSubring.nonunits ↔ InMaxG j ((ιFin R F j).base y) f) := by
  classical
  let P : Ideal ↥(chartAlgFin R F j) := y.asIdeal

  let φ₀ : ↥(chartAlgFin R F j) →+* W :=
    { toFun := fun b => ⟨(b : F), hFin b⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  let φ : ↥(chartAlgFin R F j) →+* Fbar := res.comp φ₀
  have hφ : ∀ b, φ b = res ⟨(b : F), hFin b⟩ := fun _ => rfl
  have hφu : ∀ s : P.primeCompl, IsUnit (φ s) := fun s => by
    rw [hφ]; exact (hunit s.1 s.2).map res
  let L := Localization.AtPrime P
  let ψ : Localization.AtPrime P →+* Fbar := IsLocalization.lift (M := P.primeCompl) hφu
  have hψ : ∀ b, ψ (algebraMap _ (Localization.AtPrime P) b) = φ b := fun b => IsLocalization.lift_eq hφu b
  let D : Subring Fbar := ψ.range
  let f' : Localization.AtPrime P →+* D := ψ.rangeRestrict
  have hf' : Function.Surjective f' := RingHom.rangeRestrict_surjective ψ
  haveI : IsLocalRing D := IsLocalRing.of_surjective' f' hf'
  have hrefl : ∀ m : Localization.AtPrime P, IsUnit (f' m) ↔ IsUnit m := fun m =>
    ⟨fun hu => by
      by_contra hm
      exact not_isUnit_map_of_mem_maximalIdeal f' hf' ((IsLocalRing.mem_maximalIdeal _).mpr hm) hu,
     fun hu => hu.map f'⟩

  have hKD : ∀ c : K, algebraMap K Fbar c ∈ D := by
    intro c
    obtain ⟨a, ha, he⟩ := hK c
    refine ⟨algebraMap _ (Localization.AtPrime P) (algebraMap R ↥(chartAlgFin R F j) a), ?_⟩
    rw [hψ, hφ, ← he]
    congr 1

  have hD : ∃ d : D, d ≠ 0 ∧ ¬ IsUnit d := by
    obtain ⟨b, hbP, hb0⟩ := hng
    refine ⟨f' (algebraMap _ (Localization.AtPrime P) b), ?_, ?_⟩
    · intro h0
      apply hb0
      have := congrArg (fun d : D => (d : Fbar)) h0
      simp only [f'] at this
      rw [← hφ, ← hψ]
      exact this
    · rw [hrefl]
      intro hu
      have : algebraMap _ (Localization.AtPrime P) b ∈ maximalIdeal (Localization.AtPrime P) :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P b).mpr hbP
      exact (IsLocalRing.mem_maximalIdeal _).mp this hu
  obtain ⟨Q, hQD, hiff⟩ :=
    AlgebraicCurve.Place.exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing t D hKD hD
  refine ⟨Q, fun f hst => ?_⟩
  obtain ⟨g, h, hh, hfh⟩ := hst.1 y rfl
  have hh0 : (h : F) ≠ 0 := by
    intro h0; apply hh
    have : h = 0 := Subtype.ext h0
    rw [this]; exact P.zero_mem

  obtain ⟨u, hu⟩ := hunit h hh
  let wf : W := φ₀ g * ↑u⁻¹
  have hwu : wf * u = φ₀ g := by simp [wf]
  have hwf : (wf : F) = f := by
    have h1 := congrArg (fun w : W => (w : F)) hwu
    simp only [Subring.coe_mul, hu] at h1

    exact mul_right_cancel₀ hh0 (h1.trans hfh.symm)
  have hW : f ∈ W := hwf ▸ wf.2
  have hfw : (⟨f, hW⟩ : W) = wf := Subtype.ext hwf.symm

  have hφh : IsUnit (φ h) := hφu ⟨h, hh⟩
  have key : res ⟨f, hW⟩ = ψ (IsLocalization.mk' (Localization.AtPrime P) g (⟨h, hh⟩ : P.primeCompl)) := by
    apply mul_right_cancel₀ hφh.ne_zero
    have lhs : res ⟨f, hW⟩ * φ h = φ g := by
      rw [hfw, hφ, ← map_mul]
      have : (⟨(h : F), hFin h⟩ : W) = u := hu.symm
      rw [this, hwu]
      rfl
    have rhs : ψ (IsLocalization.mk' (Localization.AtPrime P) g (⟨h, hh⟩ : P.primeCompl)) * φ h = φ g := by
      rw [← hψ h, ← map_mul]
      have := IsLocalization.mk'_spec (Localization.AtPrime P) g (⟨h, hh⟩ : P.primeCompl)
      rw [this, hψ]
    rw [lhs, rhs]
  refine ⟨hW, ?_, ?_⟩
  · rw [key]; exact hQD _ ⟨_, rfl⟩
  · rw [key]
    have hd := hiff (f' (IsLocalization.mk' (Localization.AtPrime P) g (⟨h, hh⟩ : P.primeCompl)))

    rw [show ((f' (IsLocalization.mk' (Localization.AtPrime P) g (⟨h, hh⟩ : P.primeCompl)) : D) : Fbar) =
        ψ (IsLocalization.mk' (Localization.AtPrime P) g (⟨h, hh⟩ : P.primeCompl)) from rfl] at hd
    rw [hd, hrefl, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal,
      IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime P) P]

    constructor
    · intro hg
      refine ⟨fun y₂ hy₂ => ?_, fun y'' hy'' => ?_⟩
      · obtain rfl : y₂ = y := (ιFin R F j).isOpenEmbedding.injective hy₂
        exact ⟨g, h, hh, hg, hfh⟩
      · obtain ⟨g₁, h₁, hh₁, hgh₁, hiff₁⟩ := cross_fin j y y'' hy'' g
        obtain ⟨g₂, h₂, hh₂, hhh₂, hiff₂⟩ := cross_fin j y y'' hy'' h
        refine ⟨g₁ * h₂, h₁ * g₂, ?_, Ideal.mul_mem_right _ _ (hiff₁.mp hg), ?_⟩
        · intro hmem
          rcases y''.2.mem_or_mem hmem with h1 | h2
          · exact hh₁ h1
          · exact hh (hiff₂.mpr h2)
        · simp only [Subalgebra.coe_mul]
          calc f * ((h₁ : F) * (g₂ : F)) = f * ((h₁ : F) * ((h : F) * (h₂ : F))) := by rw [hhh₂]
            _ = (f * (h : F)) * (h₁ : F) * (h₂ : F) := by ring
            _ = (g : F) * (h₁ : F) * (h₂ : F) := by rw [hfh]
            _ = (g₁ : F) * (h₂ : F) := by rw [hgh₁]
    · intro hmax
      obtain ⟨g', h', hh', hg', hfh'⟩ := hmax.1 y rfl
      have heq : g * h' = g' * h := by
        apply Subtype.ext
        simp only [Subalgebra.coe_mul]
        rw [← hfh, ← hfh']; ring
      have : g * h' ∈ P := heq ▸ Ideal.mul_mem_right _ _ hg'
      exact (y.2.mem_or_mem this).resolve_right hh'

end E140CR
end P2MW.S_ModularCurve_FullLevel_exists_reads_of_goodPt_twoChartIntegralModel_of_eq_three
