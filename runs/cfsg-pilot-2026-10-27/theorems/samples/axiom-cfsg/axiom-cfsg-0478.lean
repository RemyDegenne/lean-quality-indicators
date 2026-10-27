public section

namespace CFSG.Quasithin.Background.Harris.AutBorel

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.Lin2.Five
  CFSG.Quasithin.H13.A6

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom coe_torusHom)

section Matrices

variable {F : Type} [Field F] [CharP F 2]

theorem tauSp_mem_unipotent {g : StatedSp 2 F} (hg : g ∈ unipotent 2 F) :
    tauSp g ∈ unipotent 2 F := by
  rw [CFSG.RankThree.CentralLiftSO.Sp.mem_unipotent_iff_flag] at hg ⊢
  simp only [coe_tauSp]
  obtain ⟨h0, h1⟩ := hg
  generalize ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = M at h0 h1 ⊢
  have z10 : M (Sum.inl 1) (Sum.inl 0) = 0 := h0 _ _ (by rw [flagOrder_ι₀, flagOrder_ι₁]; decide)
  have z30 : M (Sum.inr 1) (Sum.inl 0) = 0 := h0 _ _ (by rw [flagOrder_ι₀, flagOrder_ι₃]; decide)
  have z31 : M (Sum.inr 1) (Sum.inl 1) = 0 := h0 _ _ (by rw [flagOrder_ι₁, flagOrder_ι₃]; decide)
  have z20 : M (Sum.inr 0) (Sum.inl 0) = 0 := h0 _ _ (by rw [flagOrder_ι₀, flagOrder_ι₂]; decide)
  have z21 : M (Sum.inr 0) (Sum.inl 1) = 0 := h0 _ _ (by rw [flagOrder_ι₁, flagOrder_ι₂]; decide)
  have z23 : M (Sum.inr 0) (Sum.inr 1) = 0 := h0 _ _ (by rw [flagOrder_ι₃, flagOrder_ι₂]; decide)
  have d0 := h1 (Sum.inl 0)
  have d1 := h1 (Sum.inl 1)
  have d2 := h1 (Sum.inr 0)
  have d3 := h1 (Sum.inr 1)
  refine ⟨?_, ?_⟩
  · simp only [Sum.forall, Fin.forall_fin_two, tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂,
      tauPair_ι₃, flagOrder_ι₀, flagOrder_ι₁, flagOrder_ι₂, flagOrder_ι₃]
    simp [z10, z30, z31, z20, z21, z23, d0, d1, d2, d3]
  · simp only [Sum.forall, Fin.forall_fin_two, tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂,
      tauPair_ι₃]
    simp [z10, z30, z21, z23, d0, d1, d2, d3]

end Matrices
end CFSG.Quasithin.Background.Harris.AutBorel
end
