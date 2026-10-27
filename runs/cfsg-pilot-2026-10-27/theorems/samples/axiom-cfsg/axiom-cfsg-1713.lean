public section

namespace CFSG.Sporadic.Co2Jc

open CFSG.Sporadic.Co2Smith Subgroup

open scoped commutatorElement

theorem qWord_three (a b c : ℕ) : qWord [a, b, c] = qA a * qA b * qA c := by
  simp [qWord, mul_assoc]

end CFSG.Sporadic.Co2Jc
end
