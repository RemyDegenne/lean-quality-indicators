public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace SwapP2

theorem isSolomonMember_nine (hPS : PumpSideNine) (hPD : PumpDiagNine)
    (hEx : SwapMemberResidueNineExotic) [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
    {n : ℕ} {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X}
    {D : Finset (Fin n)} {M : Subgroup X} (hs : Setting t J n e E D M) (hn : n = 9)
    (hCA : ClaimAHolds J n e E) : FooteLit.IsSolomonMember M := by
  classical
  have S := hs.sig
  obtain ⟨e₀, -, -, he₀E, -, -, he₀1, -, -, -, -, -⟩ := exists_three_of_klein S.klein
  obtain ⟨F, DF, r, hd⟩ := dataExist_holds X t J n e E D M hs e₀ he₀E he₀1
  have hFH := hCA F hd.FJ hd.Fk DF hd.DFc hd.Fs
  have he₀H : centralizer ({e₀} : Set X) ≤ Hn E :=
    hCA E S.le S.klein D S.card S.supp e₀ he₀E he₀1
  have hOr := oddCoreR_holds X t J n e E D M hs e₀ F DF r hd hFH
  obtain ⟨-, -, N₁, hN₁⟩ := pump_holds X t J n e E D M hs e₀ F DF r hd he₀H
  have hfix := hPD X t J n e E D M hs hn e₀ F DF r hd he₀H hOr hFH N₁ hN₁
  by_cases hA : ∃ m : ℕ, Odd m ∧ Nonempty (↥N₁ ⧸ pPrimeCore 2 ↥N₁ ≃* alternatingGroup (Fin m))
  · obtain ⟨m, hmo, ⟨θN⟩⟩ := hA
    have hside := hPS X t J n e E D M hs hn e₀ F DF r hd he₀H N₁ hN₁ hfix m hmo ⟨θN⟩
    obtain ⟨hm5, -⟩ := degree_le_of_pumpData hs hd hN₁ hmo θN
    have hN₁H := le_of_exact' hs hd hOr hFH hN₁ hfix hside hmo (by omega) θN
    exact isSolomonMember_of_pumpData_le hs hd he₀H hN₁ hfix hN₁H
  · push Not at hA
    exact hEx X t J n e E D S hn hs.cent M hs.le hs.pc hs.swap hs.diag hs.alt hs.small
      hs.narrow hCA ⟨e₀, F, DF, r, N₁, hd, hN₁, hfix, fun m hm => hA m hm⟩

end SwapP2
end CFSG.ComponentClassification.SolMax
end
