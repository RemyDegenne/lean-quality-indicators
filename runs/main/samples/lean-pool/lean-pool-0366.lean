@[expose] public section

noncomputable section «lp_nc_section_1»

namespace LO

namespace Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈Sg1]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

variable (L)

notation:60 p:61 " ^→[" L "] " q:60 => Language.imp L p q

variable {L}

section «lp_section_7»

open Shift

variable (L)

variable {L}

@[simp] lemma shift_falsum : L.shift ^⊥ = ^⊥ := by simp [Language.shift, construction]

end «lp_section_7»
end Arith
end LO
end «lp_nc_section_1»
end
