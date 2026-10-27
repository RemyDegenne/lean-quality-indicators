public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native CFSG.Monster.B.Co2.Native

open CFSG.Certificates CFSG.Certificates.Native Equiv

theorem pinvs_get {n : ℕ} {S : Array (Array ℕ)} {s : ℕ} (hs : s < S.size) :
    (pinvs n S)[s]! = pinvCand n S[s]! := by
  rw [pinvs, getElem!_pos _ s (by simpa using hs), Array.getElem_map, ← getElem!_pos S s hs]

end CFSG.Sporadic.HNOddCore
end
