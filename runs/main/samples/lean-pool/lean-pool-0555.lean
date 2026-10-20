@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace DenseOverlay

theorem Snapshot.encodedStoreLength_run_le_internal (program : Program)
    (input : List Bool) (fuel : ℕ) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.overlay) :
    encodedStoreLength (snapshot.run program input fuel).overlay ≤
      encodedStoreLength snapshot.overlay +
        2 * (RAM.unitTimeUpto program fuel (snapshot.decode input) *
          (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel (snapshot.decode input)) := by
  induction fuel generalizing snapshot with
  | zero => simp [Snapshot.run, RAM.unitTimeUpto, RAM.logTimeUpto]
  | succ fuel ih =>
      rw [Snapshot.run]
      have hhalted : snapshot.Halted program ↔
          RAM.Halted program (snapshot.decode input) := Iff.rfl
      by_cases hhalt : snapshot.Halted program
      · have hramHalted := hhalted.mp hhalt
        simp only [hhalt, hramHalted, ite_true, RAM.unitTimeUpto,
          RAM.logTimeUpto]
        simp
      · have hramNotHalted : ¬RAM.Halted program (snapshot.decode input) :=
          fun h => hhalt (hhalted.mpr h)
        rw [ite_eq_right hhalt]
        simp only [RAM.unitTimeUpto, RAM.logTimeUpto, hramNotHalted,
          ite_false]
        have hstep := Snapshot.encodedStoreLength_step_le_internal
          program input snapshot
        have hnextCanonical := Snapshot.step_canonical_internal
          program input snapshot hcanonical
        have htail := ih (snapshot.step program input) hnextCanonical
        have hdecode := Snapshot.decode_step_internal
          program input snapshot hcanonical
        rw [hdecode] at htail
        calc
          encodedStoreLength
                (Snapshot.run program input fuel
                  (snapshot.step program input)).overlay ≤
              encodedStoreLength (snapshot.step program input).overlay +
                2 * (RAM.unitTimeUpto program fuel
                    (RAM.step program (snapshot.decode input)) *
                    (programStaticWidth program + 1) +
                  RAM.logTimeUpto program fuel
                    (RAM.step program (snapshot.decode input))) := htail
          _ ≤ (encodedStoreLength snapshot.overlay +
                2 * (programStaticWidth program +
                  RAM.stepLogCost program (snapshot.decode input) + 1)) +
              2 * (RAM.unitTimeUpto program fuel
                    (RAM.step program (snapshot.decode input)) *
                    (programStaticWidth program + 1) +
                  RAM.logTimeUpto program fuel
                    (RAM.step program (snapshot.decode input))) :=
            Nat.add_le_add_right hstep _
          _ = encodedStoreLength snapshot.overlay +
              2 * ((1 + RAM.unitTimeUpto program fuel
                    (RAM.step program (snapshot.decode input))) *
                    (programStaticWidth program + 1) +
                  (RAM.stepLogCost program (snapshot.decode input) +
                    RAM.logTimeUpto program fuel
                      (RAM.step program (snapshot.decode input)))) := by ring

end DenseOverlay
end RegisterStore
end RAM
end Complexity
end
