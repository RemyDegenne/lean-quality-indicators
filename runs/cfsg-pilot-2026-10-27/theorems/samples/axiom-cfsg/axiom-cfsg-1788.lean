public noncomputable section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.Certificates

open CFSG.ComponentClassification.PSL3Four (TabRep Enumerates enumerates_closure)

theorem card_rhoMA_range_le :
    Nat.card rhoMA.range ≤ 72 := by
  have hdvd := Subgroup.card_dvd_of_le rhoMA_range_le
  rw [card_kA] at hdvd
  have hlt : Nat.card rhoMA.range ≠ 144 := by
    intro h
    have := Subgroup.eq_of_le_of_card_ge rhoMA_range_le (by rw [h, card_kA])
    exact rho_mPerm_not_mem (this ▸ rho_mPerm_mem)
  obtain ⟨e, he⟩ := hdvd
  rcases e with _ | _ | e
  · omega
  · omega
  · nlinarith

end CFSG.ONSchreier
end
