public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

theorem Rc9list_mul :
    ∀ a ∈ Rc9list, ∀ b ∈ Rc9list, a * b ∈ Rc9list := by
  have h := Rc9list_mul_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

end CFSG.GH74.GLS.C3.Layer2.L5
end
