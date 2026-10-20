@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5 Integration

theorem a8_material_of_trace (β C₀ : ℝ) (hTr : A8TraceLeaf β C₀) :
    ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I Φ _hΦ κ M R _θ₀ m _θm θprev T => (6 : ℝ) / 5 ≤ β →
        epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        TMaterialContract I Φ m (I.kappaSeq κ M (m - 1)) T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))) := by
  obtain ⟨CsS, hCsS, hprofG, -⟩ := a8Core β C₀ hTr
  obtain ⟨Cm, Am, C₁m, hCmReq, -, hjm⟩ := tMaterial_of_thetaProfile_contract β C₀ CsS hCsS
  obtain ⟨Lm, hP⟩ := hprofG Cm hCmReq
  exact ⟨Am, _, OnA8Instances.gate_mp (OnA8Instances.of_A7_forall hjm) hP⟩

end AVenhance.Infra.Section5.Contracts
end
end
