public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup UnbalancedLayer UnbalancedGS

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

theorem not_isDoublePair (h2An : GSThmB.Solomon2AnInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hS : SchreierFor Blueprint.Catalog) (hSchur : SolAltLit.SchurAlternatingMultiplierInput)
    (hHe : TBLit.HeldTrivialMultiplier) (hPump : AlternatingPumpUpInput) [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hU : ¬ OutcomeLocal.UOutcome X)
    (hspor : ¬ (Nonempty (X ≃* Blueprint.NativeSporadic.M11) ∨
      Nonempty (X ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (X ≃* Blueprint.NativeSporadic.Ly))) :
    ∀ (x : X) (L : Subgroup X) (m : ℕ), ¬ IsDoublePair x L m := by
  classical
  intro x₀ L₀ m₀ hP₀
  let S := {p : X × Subgroup X // ∃ m, IsDoublePair p.1 p.2 m}
  have : Nonempty S := ⟨⟨(x₀, L₀), m₀, hP₀⟩⟩
  obtain ⟨⟨⟨x, L⟩, m, hP⟩, hmax⟩ := Finite.exists_max (fun p : S => pairMeasure p.1.1 p.1.2)
  obtain ⟨y, hy, hyL, hyK, Q, hQ, hQx, hQL, hQy, hQcard⟩ := exists_sylow_centralizing hSchur hP
  have hyZ : y ∉ center X := by
    have hZ : center X = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnonab
        exact hab ((mem_center_iff.mp (h ▸ mem_top a : a ∈ center X)) b).symm
    rw [hZ, mem_bot]
    intro h
    rw [h, orderOf_one] at hy
    norm_num at hy
  obtain ⟨hTxy, hTpc, -, hcore, ⟨φ, -⟩, hyT, M, hMy, hM, hTM, hTMpc⟩ :=
    pump_setup hS hK hP.1 hy hyZ hP.2.1 hP.2.2.1 hyL hyK
  by_cases hMx : conjugate M x = M
  · obtain ⟨m', hP', hyM⟩ :=
      stable_pump_up hPump hHe hSchur hK hP hy hyZ hTxy hTpc φ hyT hMy hM hTM hMx
    exact hspor (sporadic_of_isDoublePair_of_mem h2An hCI hSchur hnonab hU hP' hyM)
  · obtain ⟨hP', P, hPp, hPK, hPcard⟩ :=
      swap_pump_up hSchur hP hy hTxy hcore φ hyT hMy hM hTM hTMpc hMx hQ hQx hQL hQy
    have h1 : Nat.card P ≤ pairMeasure y M := card_le_pairMeasure hPp hPK
    have h2 : pairMeasure y M ≤ pairMeasure x L := hmax ⟨(y, M), m, hP'⟩
    have h3 : Nat.card Q = pairMeasure x L := hQcard
    omega

end CFSG.ComponentClassification.Sol78
end
