namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits

open Set Filter MeasureTheory Metric Batches TimeWindows Zoom Spatial Enhancement Boundary

open scoped Topology unitInterval

lemma Converges.impossible {F : ℕ → Configuration} {L : Data} (hF : Converges F L)
    (emb : ∀ n, (F n).SweepEmbedding) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (hM : Tendsto (fun n => (F n).a*(F n).n) atTop atTop)
    {C : ℝ} (hC : 0≤C)
    (hcoeff : ∀ n, 4608*((F n).a:ℝ)^2*(F n).n^4 / (((F n).R:ℝ)*(F n).a^2)^3≤C)
    (herror : Tendsto (fun n => 13824*((F n).n:ℝ)^3 / (((F n).R:ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n:ℝ)/((F n).R*(F n).a)) atTop (𝓝 0)) : False := by
  obtain ⟨K,H,A,B,T,hKH,hAH,hBH,hAB,hT,hTp,hpos,hcross,hpts⟩ :=
    hF.positive_part emb hR hC hcoeff herror hshort
  obtain ⟨q,V,hV,hVT,hcommon,hVp,hVle⟩ := hF.common_positive hR K
    (hF.conditional_nullSingleton emb hR hC hcoeff herror) hT hTp (fun z hz => (hpos z hz).1)
  let ν := (L.edgeWindow q.val.2.2:Measure Labels).restrict V
  have he : ν≪(L.edge:Measure Labels) :=
    Measure.absolutelyContinuous_of_le (hVle.trans Measure.restrict_le_self)
  have hp : ν≪(L.points:Measure Labels) := (Measure.absolutelyContinuous_of_le hVle).trans hpts
  have hproj : ν.map (pairCoordinates true A B)≪volume :=
    (((Measure.absolutelyContinuous_of_le hVle).trans hcross).map
      (continuous_pairCoordinates true A B).measurable).trans (hF.crossing_signed_projection hR hM true hAB)
  have hgood : ∀ᵐ z ∂ν, L.conditional z (carrier K)≠0 ∧ z∈commonSet L q := by
    filter_upwards [ae_restrict_mem hV] with z hz
    exact ⟨(hpos z (hVT hz)).1,hcommon z hz⟩
  have hKA : Before K A := hKH.2.1.le.trans (endpoints_of_subset hAH).1
  have hKB : Before K B := hKH.2.1.le.trans (endpoints_of_subset hBH).1
  obtain ⟨φ,G,hφ,hfinite,hGaed,hid,hjoint⟩ := hF.analytic_ready hR hAB hKA hKB q
  have hF' : Converges (F∘φ) L := hF.subseq hφ
  have hR' : Tendsto (fun n => (F (φ n)).R) atTop atTop := hR.comp hφ.tendsto_atTop
  obtain ⟨E,hE,hframe⟩ := common_frame (F∘φ) q
    (fun n => (hfinite n).2.2.1) (fun n => (hfinite n).2.2.2)
  exact hF'.spatial_impossible hR' (fun n => emb (φ n)) hC (fun n => hcoeff (φ n))
    (herror.comp hφ.tendsto_atTop) q.val.2.2 hAB (fun n => (hfinite n).1)
    (fun n => (hfinite n).2.1) E hframe V hV hVp hproj
    (hF'.radial_ae (fun n => emb (φ n)) hR' (hM.comp hφ.tendsto_atTop) hC
      (fun n => hcoeff (φ n)) (herror.comp hφ.tendsto_atTop) (hshort.comp hφ.tendsto_atTop)
      hAB hKA hKB (fun n => (hfinite n).1) (fun n => (hfinite n).2.1)
      G hjoint hGaed hid ν he hp hproj q hgood E hE)

end PlanarHalving.RankLimits
end OAI
