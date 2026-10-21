namespace OAI

section

open scoped BigOperators

namespace SKGapCutoff

lemma spin_mul_halfDiff_character {n : ℕ} (s : Finset (Fin n)) (x : Spin n) (i : Fin n) :
    spin x i * halfDiff i (character s) x = if i ∈ s then character s x else 0 := by
  rw [halfDiff_character]
  split_ifs with hi
  · exact character_erase s x i hi
  · ring

end SKGapCutoff
end
end OAI
