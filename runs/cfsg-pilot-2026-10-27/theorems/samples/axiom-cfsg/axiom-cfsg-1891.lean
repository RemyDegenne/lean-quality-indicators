public section

namespace CFSG.ClassicalInvolution.Q3.E29Ker

open CFSG.ClassicalInvolution.Generic

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

open CFSG.ClassicalInvolution.Q3.E29Data

open CFSG.Certificates.CosetEnumeration

variable {X : Type} [Group X] {φ : X →* AEQ 8} {Q : Set (Subgroup X)}

namespace Lab

variable (F : Lab φ Q)

theorem eval_rels (H : Hyp φ Q) :
    ∀ r ∈ e29Rels (), evalWord (codeVal F.gen) r = 1 := by
  intro r hr
  have hr' : r ∈ (List.range 28).flatMap q8Rels29 ++ e29ConjData.map conjRel29 := hr
  rcases List.mem_append.mp hr' with h | h
  · obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp h
    have hmem : evalWord (codeVal F.gen) r ∈ (q8Rels29 j).map (evalWord (codeVal F.gen)) :=
      List.mem_map_of_mem hj
    rw [evalWord_q8Rels29] at hmem
    rcases List.mem_cons.mp hmem with h1 | hmem
    · rw [h1]
      exact F.q8_four H j
    rcases List.mem_cons.mp hmem with h2 | hmem
    · rw [h2]
      exact rl_sq_inv (F.q8_sq H j)
    rw [List.mem_singleton.mp hmem]
    exact F.q8_conj H j
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
    rw [evalWord_conjRel29, F.conj_row H hd]
    exact mul_inv_cancel _

end Lab
end CFSG.ClassicalInvolution.Q3.E29Ker
end
