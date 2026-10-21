namespace OAI

namespace CommonBasesFPRAS

namespace MachineCode

lemma make_pair {n : ℕ} (O : IndependenceOracle n) (x y z s : Word) (bits : ℕ → Bool) :
    Runs (pack 1 0) O bits (regs y x z s) (regs (pair x y) [] z s)
      (3*x.length+2) 0 (3*x.length+2) := by
  simpa only [pair,pairRegisters,update_regs_zero,update_regs_one] using
    runs_pack (k:=1) 1 0 (by decide) O (regs [] [] z s) x y bits

end MachineCode
end CommonBasesFPRAS
end OAI
