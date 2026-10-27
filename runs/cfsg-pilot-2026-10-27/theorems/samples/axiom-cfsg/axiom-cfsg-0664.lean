public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

open CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank

theorem listedMultiplierBoundAt_lie (hGA : CFSG.Open.GriessAllModelsStatement) (p : ℕ)
    (j : TauCeti.ValidLieTypeIndex) : ListedMultiplierBoundAt p (.lie j) := by
  obtain ⟨d, hv⟩ := j
  cases d with
  | A r q =>
    rcases r with _ | _ | _ | r
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
    · exact lieCase_A_one hGA p q hv
    · exact lieCase_A_two hGA p q hv
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | _ | _ | r
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
    · exact lieCase_twistedA_two hGA p q hv
    · exact lieCase_twistedA_three hGA p q hv
    · exact lieCase_twistedA_four hGA p q hv
    · exact lieCase_twistedA_five hGA p q hv
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | B r q =>
    rcases r with _ | _ | _ | _ | r
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
    · exact lieCase_B_two hGA p q hv
    · exact lieCase_B_three hGA p q hv
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | C r q => exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | D r q =>
    rcases r with _ | _ | _ | _ | _ | r
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
    · exact lieCase_D_four hGA p q hv
    · exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | twistedD r q => exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | E6 q => exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | E7 q => exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | E8 q => exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | F4 q => exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | G2 q => exact lieCase_G2 hGA p q hv
  | twistedE6 q => exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | trialityD4 q => exact lieCase_trialityD4 hGA p q hv
  | suzuki m => exact lieCase_suzuki hGA p m hv
  | reeG2 m => exact fun hi => hi.elim (fun h => h.elim) (fun h => h.2.elim)
  | reeF4 m => exact lieCase_reeF4 hGA p m hv
  | tits => exact lieCase_tits hGA p hv

end CFSG.LocalAnalysis.GLTheoremA
end
