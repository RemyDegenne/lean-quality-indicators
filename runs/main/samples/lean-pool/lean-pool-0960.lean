@[expose] public section

open Matrix

open scoped Matrix

namespace BollobasNikiforov

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable {R : Type*} [CommRing R]

noncomputable section

open Finset

variable {k p : ℕ}

lemma idxZ_injective {i h : Fin k} (heq : (idxZ (p := p) i : ConfigIdx k p) = idxZ h) :
    i = h := by
  have := congrArg Fin.val heq
  simp only [idxZ_val, Nat.add_right_cancel_iff] at this
  exact Fin.ext this

end
end BollobasNikiforov
end
