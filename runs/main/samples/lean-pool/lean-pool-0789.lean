@[expose] public section

noncomputable section «lp_nc_section_1»

namespace LO

namespace Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

variable {T : L.Theory} {pT : pL.TDef} [T.Defined pT]

section «lp_section_1»

variable (L)

variable {L}

variable (L)

variable {L}

section «lp_section_5»

@[simp] lemma seq_lt_andIntro (s p q dp dq : V) :
    s < andIntro s p q dp dq :=
  le_iff_lt_succ.mp <| le_pair_left _ _

end «lp_section_5»
end «lp_section_1»
end Arith
end LO
end «lp_nc_section_1»
end
