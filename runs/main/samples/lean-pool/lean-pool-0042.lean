@[expose] public section

namespace GaleStewartGame.BorelDet.Zero

open Stream'.Discrete Descriptive Tree Game PreStrategy

open CategoryTheory

variable {A : Type*} {G : Game A} {k : ℕ} {hyp : Hyp G k} {m n : ℕ}

noncomputable section «Section1»

variable (H : PreLift hyp)

namespace PreLift

@[simp] lemma take_rfl : H.take (H.x.val.length (α := no_index _)) H.hlvl = H :=
  H.take_of_length_le le_rfl

end PreLift
end «Section1»
end GaleStewartGame.BorelDet.Zero
end
