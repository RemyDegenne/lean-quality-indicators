namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingFinish

open Turing BinPackingGames.Foundations.Complexity

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters

open BinPackingGames.Reduction.MachineTransfer

variable (fixed : InventoryData) (K : Nat)

theorem finish_exec (base : Tape fixed K → List Bool) (state : State) (word : List Bool)
    (reverseWord : base (.inr .reverseOutput) = word.reverse)
    (outputEmpty : base (.inr .output) = []) :
    Exec (GraphPackingProgram.finish fixed K) ⟨state, base⟩ (word.length + 5)
      ⟨.arithmetic (BinaryAddMachine.clean ()), resultTapes fixed K base word⟩ := by
  let push : Action (Tape fixed K) State :=
    .push (.inr .reverseOutput) (fun _ => false) .done
  let pushed := Function.update base (.inr Extra.reverseOutput) (false :: word.reverse)
  have first : Exec (.atom push) ⟨state, base⟩ 1 ⟨state, pushed⟩ := by
    simpa only [push, pushed, Action.eval, reverseWord] using Exec.atom push ⟨state, base⟩
  have second := PackingArithmeticProgram.exec (transfer fixed K) pushed
    (resultTapes fixed K base word) (word.length + 2) state
    (transfer_exec fixed K base word reverseWord outputEmpty)
  have third := Exec.atom (K := Tape fixed K) (S := State) .done
    ⟨.arithmetic (BinaryAddMachine.clean ()), resultTapes fixed K base word⟩
  have joined := Exec.seq first (Exec.seq second third)
  simpa only [GraphPackingProgram.finish, GraphPackingProgram.chain, transfer, push,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_comm, Nat.add_left_comm, Action.eval] using joined

end BinPackingGap.GraphPackingFinish
end
end OAI
