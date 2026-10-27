public section

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

section Aut

theorem permVal_comm {π : Equiv.Perm (Fin 128)} (hπ : π ∈ AutC) {c d : ℕ} (hc : c < 128)
    (hd : d < 128) (hdfix : permVal π d = d) (hrowc : ∀ u < 128, mulC c u = 0 → u = invC c)
    (hrowd : ∀ u < 128, mulC d u = 0 → u = invC d) (hcd : commC c d = 0 ∨ commC c d = tC) :
    commC (permVal π c) d = commC c d := by
  have hinvc : invC (permVal π c) = permVal π (invC c) := by
    obtain ⟨y, hy, hyv⟩ := permVal_surj π (invC_lt (permVal_lt π hc))
    have h1 : permVal π (mulC c y) = permVal π 0 := by
      rw [permVal_mul hπ hc hy, hyv, mulC_invC (permVal_lt π hc), permVal_zero hπ]
    have h2 : mulC c y = 0 := permVal_inj π (mulC_lt hc hy) (by norm_num) h1
    rw [← hyv, hrowc y hy h2]
  have hinvd : permVal π (invC d) = invC d := by
    have h1 : mulC d (permVal π (invC d)) = 0 := by
      have h := permVal_mul hπ hd (invC_lt hd)
      rw [mulC_invC hd, permVal_zero hπ, hdfix] at h
      exact h.symm
    exact hrowd _ (permVal_lt π (invC_lt hd)) h1
  have hX : mulC (permVal π c) d = permVal π (mulC c d) := by
    rw [permVal_mul hπ hc hd, hdfix]
  have hY : mulC (invC (permVal π c)) (invC d) = permVal π (mulC (invC c) (invC d)) := by
    rw [hinvc, permVal_mul hπ (invC_lt hc) (invC_lt hd), hinvd]
  have hcd' : mulC (mulC c d) (mulC (invC c) (invC d)) = 0 ∨
      mulC (mulC c d) (mulC (invC c) (invC d)) = tC := hcd
  unfold commC
  rw [hX, hY, ← permVal_mul hπ (mulC_lt hc hd) (mulC_lt (invC_lt hc) (invC_lt hd))]
  exact permVal_fix hπ (by
    rcases hcd' with h | h
    · exact Or.inl h
    · exact Or.inr h)

end Aut
end CFSG.EvenSporadicStandard.Fin76b.W16
end
