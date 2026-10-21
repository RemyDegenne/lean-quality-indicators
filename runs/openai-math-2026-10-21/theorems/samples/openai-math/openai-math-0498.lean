namespace OAI

section

namespace MinUncutGames.Foundations.Complexity.MachineOverlayTable

open Turing MachineComposition

open PCP PCP.GraphTables PCP.PreprocessingOverlayWords

open MachineCloudPadding

variable {A : Type} {d e : Nat}

theorem outputPrefix_length_le {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (k : Nat) :
    (outputPrefix G H k).length ≤ outputCapacity d e n := by
  have hblocks := flatten_length_le ((List.ofFn (outputBlock G H)).take k)
    (blockSize d e n) (by
      intro xs hx
      have hm := List.mem_of_mem_take hx
      obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hm
      exact outputBlock_length_le G H v)
  have hlen : ((List.ofFn (outputBlock G H)).take k).length ≤ n := by
    simp only [List.length_take, List.length_ofFn]
    exact Nat.min_le_right _ _
  have hcap := Nat.mul_le_mul_right (blockSize d e n) hlen
  simp only [outputPrefix, emittedPrefix, List.length_append, encodeWords_length,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil, Nat.add_zero, outputCapacity]
  omega

end MinUncutGames.Foundations.Complexity.MachineOverlayTable
end
end OAI
