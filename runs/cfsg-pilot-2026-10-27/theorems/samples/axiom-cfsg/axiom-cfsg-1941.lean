public section

namespace CFSG.RankThree.PartOne.HNRed

open Polynomial Module

section Spaces

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem Ypow_mem_eSpace {X Z Y Yi : Module.End k V} (hYiY : Yi * Y = 1) (hYZ : Y * Z = Z * Y)
    (hYX : Y * X * Yi = X * Z) {j : ℕ} {w : V} (n : ℕ) (hw : w ∈ eSpace X Z j) :
    (Y ^ n) w ∈ eSpace X Z (j + n) := by
  induction n with
  | zero => simpa using hw
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact Y_mem_eSpace hYiY hYZ hYX ih

end Spaces
end CFSG.RankThree.PartOne.HNRed
end
