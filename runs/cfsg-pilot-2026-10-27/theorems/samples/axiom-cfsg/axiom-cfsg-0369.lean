public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action
  CFSG.QuasithinUnique.A5.Split

theorem exists_u9data
    (h247 : Lemma2_4_27) (h245_4 : Lemma245_4) (hC54 : LemmaC54_3)
    (h314 : A314A5Excluded) {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}
    (cfg : A5Cfg G T M H S L) {z u : G} (s7 : A5Step7 T M H S L z u) :
    ∃ A V : Subgroup G, U9Data T M H S L z u A V := by
  have h27 : Lemma2_4_27Concl T H S L :=
    h247 G T M H S L cfg.cs (Or.inl ⟨cfg.alt5, cfg.single⟩)
  have hRx : ∀ x ∈ T, x ∉ S → baum S = blockU L ⊔ conjR (blockU L) x := by
    intro x hx hxS
    have h4 := (h27.2.2.2 x hx hxS).1
    rwa [s7.TC_one, bot_sup_eq, blockU0_eq_blockU cfg.single] at h4
  have key : ∀ (C : StdCfg T M H S L), Sec C → u = C.u0 →
      ∃ A V : Subgroup G, U9Data T M H S L z u A V := by
    intro C X hu0
    have hzz : z = C.zU := X.z_eq s7.z_gen
    refine ⟨X.A4W, X.V4W, ?_⟩
    exact
      { s7 := s7
        U_comm := fun a ha b hb => C.U_comm ha hb
        U_sq := fun a ha => cfg.cs.block.1.1.2.2.1.2 a ha
        A_eq := by rw [hu0]; exact X.pResidual_Hu.symm
        hA := X.isA4Block_A4W
        V_le := X.V4W_le_U
        uz_mem := by rw [hu0, hzz]; exact X.uz_mem_V4W
        R_eq := hRx
        Tu_card := by
          have h := X.card_Tu (hu0 ▸ s7.u_mem)
          rw [hu0]
          exact h
        U_card := C.card_U }
  obtain ⟨C, ⟨X⟩⟩ := a5_exists_sec h247 h245_4 hC54 h314 cfg
  rcases X.exists_w_of_Z s7.u_mem s7.u_not with h | h
  · exact key C X h
  · let C' : StdCfg T M H S L :=
      C.relabel rho13 (fun σ hσ => rho13_conj_E σ hσ) (fun σ hσ => rho13_conj_E' σ hσ)
    obtain ⟨X'⟩ := exists_sec C' s7.TC_one
    have hu' : u = C'.u0 := by
      rw [h]
      show _ = ((C.iV (vact rho13⁻¹ g1w) : ↥H) : G)
      rw [rho13_inv, vact_rho13_g1w]
    exact key C' X' hu'

end CFSG.QuasithinUnique.A5
end
