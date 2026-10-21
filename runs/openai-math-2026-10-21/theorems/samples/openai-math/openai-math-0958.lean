namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory

open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.projected_source_structural_edge_log_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤ C ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤ T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤ a → b≤ T → a≤ b → b-a≤(w/P)^2 →
      0< M → 0≤ A → 1≤ P → 1≤ Real.log (2+P) → 0< w → w≤ P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤ P) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let E := ∫x : Vec,totalEnergy s (0,x)
      let edge : Set (Fin 4→ℕ) := {k | cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1) ∧
        cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/16}
      (∑'k : Fin 4→ℕ,edge.indicator (fun k=>∫⁻z : ConeCoordinate,
          physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
            ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal (C*(1+E)*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5) := by
  classical
  obtain ⟨C,hC,hbound⟩ := hd₀.source_majorant_remaining_log_sum
  obtain ⟨c,hc,hcut⟩ := dyadicFactor_log_derivative_bound
  let D := 64+5880000*c
  have hD : 0≤ D := by dsimp [D]; positivity
  refine ⟨D*C,by positivity,?_⟩
  intro s T F hs hT h0 zX S Q a b w M A P hS hS0 ha hb hab hJI hM hA hP hL hw hwP hsource hW HX HZ
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := fun k=>representativeClosedBin T w k
  let edge : Set (Fin 4→ℕ) := {k | cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1) ∧
    cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/16}
  let sector : Set (Fin 4→ℕ) := {k | cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1)}
  have hj : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hα := (F.continuous_prefixFlow hs hT).comp
    (continuous_id.prodMk continuous_const : Continuous (fun t : ℝ=>(t,zX)))
  have hpoint (k : Fin 4→ℕ) : edge.indicator (fun k=>∫⁻z : ConeCoordinate,
      physicalProjectedSourceDensity s X V (B k) T w Q z ∂physicalBinMeasure V (B k) (Icc a b)) k ≤
    ENNReal.ofReal D*sector.indicator (fun k=>∫⁻z : ConeCoordinate,
      physicalSourceMajorantDensity s X V (B k) z ∂physicalBinMeasure V (B k) (Icc a b)) k := by
    by_cases hk : k∈edge
    · rw [Set.indicator_of_mem hk,Set.indicator_of_mem (show k∈sector from hk.1)]
      apply physicalProjectedSourceIntegral_le_majorant (X:=X) (V:=V) hs hα.snd.measurable (B k) Q measurableSet_Icc hj hc hcut hw
      · intro t ht
        simp only [V,prefixFlow,prefixClamp_eq (hj ht)]
        exact hW t ht
      · change 0< max 1 T*cappedRepresentative (k 3)/2
        exact div_pos (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (cappedRepresentative_pos _)) (by norm_num)
      · apply representativeClosedBin_small_of_angle
        have hφ := cappedRepresentative_pos (k 2)
        linarith only [hk.2,hφ]
    · rw [Set.indicator_of_notMem hk]
      exact bot_le
  apply (ENNReal.tsum_le_tsum hpoint).trans
  rw [ENNReal.tsum_mul_left]
  apply (mul_le_mul' le_rfl (hbound s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hab hJI
    hM hA hP hL hw hwP hsource HX HZ)).trans_eq
  rw [←ENNReal.ofReal_mul hD]
  congr 1
  ring

end RVM
end
end
end OAI
