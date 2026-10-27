public section

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

open scoped commutatorElement

namespace CFSG.GH74.Generic.S45.EvSpor

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Certificates.Native
  CFSG.ComponentClassification.J2Cover

theorem j2_Kb_facts
    (h : j2KbEnumOK = true) :
    EnumsSub 315 j2Kb (closure (tp 315 '' {x | x ∈ j2KbGens.toArray})) ∧
      Nat.card ↥(closure (tp 315 '' {x | x ∈ j2KbGens.toArray})) = 60 ∧
      closure (tp 315 '' {x | x ∈ j2KbGens.toArray}) ≤ j2P ∧
      Rep 315 j2KbA (tp 315 j2KbA) ∧ Rep 315 j2KbB (tp 315 j2KbB) := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  rw [j2KbEnumOK, Bool.and_eq_true] at h
  obtain ⟨hE, hc, hrep⟩ := enumOK_spec hn h.1
  exact ⟨hE, hc, j2_gens_mem hrep h.2, hrep _ (by simp [j2KbGens]), hrep _ (by simp [j2KbGens])⟩

end CFSG.GH74.Generic.S45.EvSpor
end
