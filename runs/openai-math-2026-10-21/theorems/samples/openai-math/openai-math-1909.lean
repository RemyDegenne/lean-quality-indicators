namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel

open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]

variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]

variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)

variable [∀ a, Fintype (B a)]

variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]

variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

variable (S : LayerSamplerScale (G := G) B U b R σ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))

local notation "jetRows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "fullRows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

theorem allocatedProductKernelData_normalized
    {Psp E e pNum Pbase pAccuracy pSampling l F : ℝ} (hP : 0 ≤ Psp) (hE : 0 ≤ E)
    (hPbase : Psp ≤ Pbase) (hpNum : pNum ≤ Pbase)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ Psp) (hdim : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (hG : (Fintype.card G : ℝ) ≤ Psp) (hl : Pbase ≤ l) (hF : 0 ≤ F)
    (hnum : ∀ (_o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
      (C V : Fin m → ℝ≥0), (∀ j, (C j : ℝ) ≤ Real.exp pNum) →
      (∀ j, (V j : ℝ) ≤ Real.exp pNum) → AllocatedSourceNumerics B U b S C V Pbase)
    {δ : ℝ≥0} {A Kraw Ksite Knorm : ℕ}
    (hKraw : 1 ≤ Kraw) (hKsite : 1 ≤ Ksite) (hKnorm : 1 ≤ Knorm)
    (hnorm : AllocatedSourceNarrowNormalization.{uG,uI,uB,uJ,uX} m Knorm)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val) :
    let Qraw := allocatedSourceSamplingBudget m dim A Pbase (E + 1) l F
    AllocatedProductKernelData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw Ksite witnesses →
    AllocatedProductNormalizedKernelData.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pNum Pbase Qraw pAccuracy pSampling hP δ A Kraw (max Ksite Knorm) witnesses := by
  intro Qraw hKernel
  have hPbase0 : 0 ≤ Pbase := hP.trans hPbase
  have hEsource : 0 ≤ E + 1 := by linarith
  have hQraw1 : 1 ≤ Qraw :=
    (allocatedSourceSamplingBudget_bounds m dim A hPbase0 hEsource (hPbase0.trans hl) hF).1
  have hQraw0 : 0 ≤ Qraw := zero_le_one.trans hQraw1
  unfold AllocatedProductNormalizedKernelData
  intro w v Pfinal Mk hMk selection hqDim hMkPsp Kernel Good GoodKernel
  have hFinal := sourceCoverParameter_bounds dim Kraw (pNum := pNum) (Qraw := Qraw)
    (F := allocatedSiteErrorFourierOutput m pSampling w v)
    (G := allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 1)) hP
  have hFinal0 : 0 ≤ Pfinal := zero_le_one.trans hFinal.1
  have hRawPower : Qraw ≤ (Qraw + Kraw) ^ Kraw := by
    have h := shifted_power_self_mono hQraw0 (le_refl 1) hKraw
    simp only [Nat.cast_one, pow_one] at h
    linarith
  have hRawFinal : Qraw ≤ Pfinal := hRawPower.trans hFinal.2.2.2.2.1
  have hOldCut : Real.exp ((Pfinal + Ksite) ^ Ksite) ≤
      Real.exp ((Pfinal + (max Ksite Knorm : ℕ)) ^ max Ksite Knorm) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hFinal0 hKsite (le_max_left _ _))
  have hNormCut : Real.exp ((Qraw + Knorm) ^ Knorm) ≤
      Real.exp ((Pfinal + (max Ksite Knorm : ℕ)) ^ max Ksite Knorm) := by
    apply Real.exp_le_exp.mpr
    exact (pow_le_pow_left₀ (add_nonneg hQraw0 (Nat.cast_nonneg _))
      (add_le_add hRawFinal le_rfl) Knorm).trans
      (shifted_power_self_mono hFinal0 hKnorm (le_max_right _ _))
  obtain ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, hKernel⟩ :=
    hKernel hMk selection hqDim hMkPsp
  let _ : ∀ x, NeZero (d x) := fun x => ⟨(hd x).ne'⟩
  let _ : ∀ x, NeZero (modulus x) := fun x => ⟨(hmodulus x).ne'⟩
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy Cinv hCinv hchart hsmall
    hσ1 hproductSmall μ _ _ ν _ _ _ _ _ μsmall _ _ X _ _ hXPsp q hq hqPsp refined index _
    W hW indices ξ hξ sourceMesh mesh τ hτ hτP N hN hsizeN poly hpoly hmem
    rank hrank hRank cells hcells test htest bases hbases V₀ Z H law
    coverValue wholeReference reconstruct weight cover
  obtain ⟨_, hnormal⟩ := hnorm B U b S hb o μ ν hR hσ hσ1 C V hC hV Cinv hCinv hchart
    hsmall A (hnum o C V hCp hVp) hP hEsource hPbase hm hdim hG hl hF
    hXPsp selection hMk hMkPsp q hq hqPsp hτ (hτP.trans (Real.exp_le_exp.mpr hpNum))
    N (fun t => hNormCut.trans (hsizeN t)) poly hpoly hmem hrank (hNormCut.trans hRank) cells hcells
  have hZ := hnormal bases hbases
  obtain ⟨hmass, hcomparison⟩ := hKernel block hb o bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy
    Cinv hCinv hchart hsmall hσ1 hproductSmall μ ν μsmall hXPsp q hq hqPsp hτ hτP N hN
    (fun t => hOldCut.trans (hsizeN t)) poly hpoly hmem hrank (hOldCut.trans hRank)
    cells hcells test htest bases hbases hZ.2.1.1
  exact ⟨hmass, hZ, hcomparison⟩

end Erdos3.VectorPolynomial
end
end OAI
