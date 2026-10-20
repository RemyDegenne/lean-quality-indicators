@[expose] public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse

theorem cellReg_decode_internal (n reg : ℕ) (hreg : cellBase n ≤ reg) :
    cellReg n (decodeCellTape n reg) (decodeCellPosition n reg) = reg := by
  have hdivision := Nat.mod_add_div (reg - cellBase n) (n + 2)
  rw [Nat.mul_comm (n + 2)] at hdivision
  simp only [cellReg, decodeCellTape, decodeCellPosition]
  omega

end Sparse
end TMConfig
end RAM
end Complexity
end
