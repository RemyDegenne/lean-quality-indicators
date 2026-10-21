namespace OAI

noncomputable section

namespace ElasticityGeneralSlicing

open Set MeasureTheory TemperedDistribution Filter

open scoped SchwartzMap ENNReal BigOperators Topology LineDeriv

open ElasticitySlicing

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
    [Measure.IsAddHaarMeasure (volume : Measure P)]

open ElasticityPlanar ElasticityRegularity

open ElasticityPlanarDistribution (Dist dbar)

variable {n : Type*} [Fintype n]

theorem coupled_slice_equations (S K : Set ℂ) (hS : IsCompact S) (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j t z,z∉K → a i j (t,z)=0)
    (f : n → P × ℂ → ℂ) (hf : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfs : ∀ i t z,z∉K → f i (t,z)=0)
    (u w : n → Lp ℂ 2 (volume : Measure (P × ℂ)))
    (hu : ∀ i,Integrable (u i : P × ℂ → ℂ)) (hw : ∀ i,Integrable (w i : P × ℂ → ℂ))
    (hsu : ∀ i,∀ᵐ q : P × ℂ,q.2∉S → u i q=0)
    (hsw : ∀ i,∀ᵐ q : P × ℂ,q.2∉S → w i q=0)
    (hc : ∀ i,∀ᵐ q : P × ℂ,w i q=∑ j,a i j q*u j q-f i q)
    (he : ∀ i, ∂_{((0:P),(1:ℂ))} (u i : 𝓢'(P × ℂ,ℂ))+
      Complex.I • ∂_{((0:P),Complex.I)} (u i : 𝓢'(P × ℂ,ℂ))+(w i : 𝓢'(P × ℂ,ℂ))=0) :
    ∀ᵐ t : P, ∀ i,
      planarOperator (fun i j z => a i j (t,z)) i
        (WithLp.toLp 2 (fun j => sliceLp (u j) t))=
        (toSchwartz ⟨fun z => f i (t,z),⟨(hf i).comp (contDiff_const.prodMk contDiff_id),
          compact_slice hK (f i) (hfs i) t⟩⟩ : Dist) ∧
      LocalEqual Sᶜ (sliceLp (u i) t : Dist) 0 := by
  classical
  have hsl : ∀ᵐ t : P, ∀ i,
      dbar (sliceLp (u i) t : Dist)+(sliceLp (w i) t : Dist)=0 ∧
      LocalEqual Sᶜ (sliceLp (u i) t : Dist) 0 := by
    rw [ae_all_iff]
    exact fun i => cylinder_supported_slices S hS (u i) (w i) (hu i) (hw i) (hsu i) (hsw i) (he i)
  have huc : ∀ᵐ t : P,∀ i, MemLp (fun z => u i (t,z)) 2 volume := by
    rw [ae_all_iff]
    exact fun i => memLp_two_slices (Lp.memLp (u i))
  have hwc : ∀ᵐ t : P,∀ i, MemLp (fun z => w i (t,z)) 2 volume := by
    rw [ae_all_iff]
    exact fun i => memLp_two_slices (Lp.memLp (w i))
  have hcc : ∀ᵐ t : P,∀ i,∀ᵐ z : ℂ,w i (t,z)=∑ j,a i j (t,z)*u j (t,z)-f i (t,z) := by
    rw [ae_all_iff]
    exact fun i => Measure.ae_ae_of_ae_prod (hc i)
  filter_upwards [hsl,huc,hwc,hcc] with t ht hut hwt hct
  intro i
  refine ⟨?_,(ht i).2⟩
  let ft : Test := ⟨fun z => f i (t,z),⟨(hf i).comp (contDiff_const.prodMk contDiff_id),
    compact_slice hK (f i) (hfs i) t⟩⟩
  have hac (j : n) : (fun z => a i j (t,z)).HasTemperateGrowth :=
    (compact_slice hK (a i j) (hs i j) t).hasTemperateGrowth
      ((ha i j).comp (contDiff_const.prodMk contDiff_id))
  have hrel : ∀ᵐ z : ℂ,sliceLp (w i) t z=∑ j,a i j (t,z)*sliceLp (u j) t z-ft z := by
    have huall : ∀ᵐ z : ℂ,∀ j,sliceLp (u j) t z=u j (t,z) := by
      rw [ae_all_iff]
      exact fun j => sliceLp_coe (hut j)
    filter_upwards [sliceLp_coe (hwt i),huall,hct i] with z hwz huz hcz
    simpa only [hwz,huz] using hcz
  have hh := sliced_coefficients (fun j z => a i j (t,z)) hac
    (fun j => sliceLp (u j) t) (sliceLp (w i) t) ft hrel
  have hz := (ht i).1
  rw [hh] at hz
  rw [planarOperator_apply]
  change dbar (sliceLp (u i) t : Dist)+∑ j,smulLeftCLM ℂ (fun z => a i j (t,z))
    (sliceLp (u j) t : Dist)=(toSchwartz ft : Dist)
  exact sub_eq_zero.mp (by simpa only [add_sub_assoc] using hz)

end ElasticityGeneralSlicing
end
end OAI
