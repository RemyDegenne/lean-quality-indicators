@[expose] public section

section SourceQuantumChordWindow

namespace QuantumQueryComplexity

open scoped Matrix

open Matrix

variable {H : Type} [Fintype H] [DecidableEq H]

lemma isSelfAdjoint_chordSq (U : Matrix H H ℂ) : IsSelfAdjoint (chordSq U) := by
  change star (chordSq U) = chordSq U
  rw [Matrix.star_eq_conjTranspose]
  exact chordSq_conjTranspose U

end QuantumQueryComplexity
end SourceQuantumChordWindow
end
