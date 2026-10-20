@[expose] public section

namespace LO

namespace Arith

open FirstOrder FirstOrder.Arith

noncomputable section «lp_nc_section_1»

variable {V : Type*} [ORingStruc V]

section «lp_section_1»

variable [V ⊧ₘ* 𝐈open]

section «lp_section_4»

prefix:75 "√" => sqrt

@[simp] lemma sqrt_four : √(4 : V) = 2 := by simp [←two_mul_two_eq_four]

end «lp_section_4»
end «lp_section_1»
end «lp_nc_section_1»
end Arith
end LO
end
