public section

namespace CFSG.ClassicalInvolution.PhanDn

open SimpleGraph CFSG.ClassicalGroups.Unitary CFSG.Monster.B.Recog

open CFSG.ClassicalInvolution.Phan.Geometry

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem exists_reduce_solid_line (hσ : IsUnitaryInvolution σ) {u v : FlagVert σ 3}
    (hu4 : Module.finrank K u.1 = 4) (hv : Module.finrank K v.1 = 2)
    (h : (flagGraph σ 3).Adj u v) (hvu : v.1 < u.1) :
    ∃ q : (compGraph σ).Walk (retractCompVert hσ u) (retractCompVert hσ v),
      CompHedge hσ h q := by
  have hune : Module.finrank K u.1 ≠ 2 := by omega
  let U0 : CompVert σ := ⟨u, hune⟩
  let V0 : CompVert σ := chosenLinePoint hσ v hv
  have eu : retractCompVert hσ u = U0 := retractCompVert_ret hσ hune
  have ev : retractCompVert hσ v = V0 := retractCompVert_line hσ hv
  have hVP : (flagGraph σ 3).Adj V0.1 v := chosenLinePoint_adj hσ v hv
  have hPV : (flagGraph σ 3).Adj u V0.1 :=
    Or.inr (Or.inl (lt_trans (chosenLinePoint_lt hσ v hv) hvu))
  let q0 : (compGraph σ).Walk U0 V0 := Walk.cons (Or.inl hPV) Walk.nil
  let cu0 : (flagGraph σ 3).Walk u U0.1 := Walk.nil
  let cv0 : (flagGraph σ 3).Walk v V0.1 := Walk.cons hVP.symm Walk.nil
  have H0 : Homotopic (cu0.append
      (substituteWalk (compIncl σ) (fun {U W : CompVert σ}
        (e : (compGraph σ).Adj U W) => expandCompEdge e) q0))
      ((Walk.cons h Walk.nil).append cv0) := by
    dsimp only [cu0, cv0, q0]
    erw [substituteWalk_cons, substituteWalk_nil, expandCompEdge_of_flagGraph hPV]
    exact (homotopic_triangle_path h hVP.symm hPV).symm
  refine ⟨q0.copy eu.symm ev.symm, ?_⟩
  exact hedge_of_copies hσ eu ev q0 cu0 cv0 h H0
    (retractConnector_ret hσ hune) (retractConnector_line hσ hv)

end CFSG.ClassicalInvolution.PhanDn
end
