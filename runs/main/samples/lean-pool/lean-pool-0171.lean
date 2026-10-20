@[expose] public section

namespace PDL

namespace LoadedCluster

variable {X : Sequent} {tab : Tableau .nil X} {C : LoadedCluster tab}

lemma satDown_three_not_basic {Δ next} (hS : C.SatDownFacts) (hΔ : Δ ∈ C.lambdaTwo)
    (hb : ¬ Δ.basic) (hx : C.Q.atOpt x = some (.QNode .three Δ next))
    (hlen : next.length = (C.stepOfL Δ).length)
    (hlab : ∀ i, (hi : i < (C.stepOfL Δ).length) →
      C.Q.labelAt (x ++ [i]) = some ((C.stepOfL Δ)[i]'hi))
    (IH : ∀ i, i < next.length → C.SatDown θ (x ++ [i])) : C.SatDown θ x := by
  intro W M g v Z hxlab hZ hι
  have hZeq : Δ = Z := by rw [QuasiTab.labelAt, hx] at hxlab; simpa using! hxlab
  subst hZeq
  have hcomp : x ∉ C.Q.companions := by
    intro hcon
    have := C.Q.typAt_of_mem_companions hcon
    rw [QuasiTab.typAt, hx] at this
    simp [QuasiTab.typ] at this
  obtain ⟨i, hi, hright, hwd⟩ := hS.nonBasicStep Δ hΔ hb W M v hZ
  have hi' : i < next.length := by omega
  rw [C.iitp_three_not_basic hx hb, QFormula.evalQ_conj] at hι
  have hii : QFormula.evalQ M g v (C.iitp θ (x ++ [i])) := by
    refine hι _ ?_
    rw [← C.iitpList_getElem_eq_iitp hx hi']
    exact List.getElem_mem _
  obtain ⟨z, hz, Y, u, h1, h2, h3, h4, h5⟩ :=
    IH i hi' W M g v _ (hlab i hi) hright hii
  refine ⟨z, QuasiTab.cycs_subset_of_qedge _ hcomp (QuasiTab.qedge_snoc hx hi') z hz,
    Y, u, h1, h2, h3, hwd ▸ h4, fun hbb => hwd ▸ h5 (hbb.child
      (QuasiTab.prefix_of_mem_cycs hz) (by simp) (QuasiTab.notBasic_of_label hx hb))⟩

end LoadedCluster
end PDL
end
