@[expose] public section

namespace BeyondBethe

open Complexity

theorem machineDirectedLogNumeratorAbsBits_encode
    (ruler : List Bool) (q : ℚ) :
    machineDirectedLogNumeratorAbsBits
        (pair ruler (rawRatBinaryCode (rawRatOfRat q))) = q.num.natAbs.bits := by
  rw [machineDirectedLogNumeratorAbsBits]
  simp only [machineDirectedLogArgumentCode, machinePairSecond_pair,
    rawRatBinaryCode, machinePairFirst_pair,
    machineIntegerNatAbsBits_encode, rawRatOfRat]

end BeyondBethe
end
