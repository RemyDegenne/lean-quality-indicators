public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank

open CFSG.SeitzReduction.E8Pilot CFSG.StandardType.MpTypeDet CFSG.StandardType.NbrInnerMore

open CFSG.SeitzReduction.E8Pilot CFSG.StandardType.MpTypeDet CFSG.StandardType.NbrInnerMore

theorem excOrd_G2_ne_Suzuki {g f : ℕ} (hg : 2 ≤ g) (hf : 1 ≤ f) :
    ordG2 (2 ^ g) ≠ ordSuzuki (2 ^ f) := by
  intro h
  have h1 := CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordG2' (by omega : 1 ≤ g)
  rw [h] at h1
  obtain ⟨hN, hZ⟩ := h1.transfer (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordSuzuki' hf)
  have hk := (hZ (g * 6) (by omega) (by omega)).mp (Or.inl dvd_rfl)
  rcases hk with ⟨-, h3⟩ | h2
  · exact (h3 (by rw [← hN])).elim
  · have := Nat.le_of_dvd (by omega) h2
    omega

end CFSG.LocalAnalysis.GLTheoremA
end
